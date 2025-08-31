// mod_weather_vibe.cpp — v5.0 (brace-enforced style)
// Packet mode (no playbooks/windows). Uses WeatherState + direct packet push (WorldPackets::Misc::Weather).
// Resends last-applied on login/zone-change. No WeatherMgr / Weather objects.
// ---------------------------------------------------
// v5 additions:
// - Weighted per-zone/daypart model from .conf
// - Fade-out → Fade-in → Dwell scheduler (interval-driven)
// - Global knobs: IntervalSec, Zone.Repeat.Max, Fade.StepValue, Fade.StepDuration.[Min|Max], Scheduler.Spread.MaxOffsetSec
// - .wvibe show enhanced: prints phase/steps/dwell/repeats per active zone
//
// This file contains your original v4.4 foundation (unchanged logic) plus additive code.
// Minimal intrusions: we only replaced HandleWvibeReload/HandleWvibeShow, and registered a new WorldScript scheduler.

#include "ScriptMgr.h"
#include "Chat.h"
#include "ChatCommand.h"
#include "Config.h"
#include "Player.h"
#include "World.h"
#include "WorldSession.h"
#include "WorldSessionMgr.h"
#include "Log.h"
#include "GameTime.h"
#include "MiscPackets.h"

#include <algorithm>
#include <cctype>
#include <cstdio>
#include <iomanip>
#include <sstream>
#include <string>
#include <unordered_map>
#include <ctime>
#include <cmath>
#include <array>
#include <vector>

using Acore::ChatCommands::ChatCommandTable;
using Acore::ChatCommands::Console;

// ===============================
// constants, enums, structs (top)
// ===============================
namespace
{
    constexpr float kMinGrade = 0.0001f;
    constexpr float kMaxGrade = 0.9999f;

    // Season awareness (auto-derived or forced via config)
    enum class Season : uint8
    {
        SPRING = 0,
        SUMMER,
        AUTUMN,
        WINTER
    };

    // DayPart awareness (auto-derived or forced via config)
    enum class DayPart : uint8
    {
        MORNING = 0,
        AFTERNOON,
        EVENING,
        NIGHT,
        COUNT
    };


    struct Range { float min = 0.0f; float max = 1.0f; };

    struct DayPartStarts
    {
        int morning = 6 * 60;     // 06:00
        int afternoon = 12 * 60;  // 12:00
        int evening = 18 * 60;    // 18:00
        int night = 22 * 60;      // 22:00
    };

    struct LastApplied
    {
        WeatherState state = WEATHER_STATE_FINE;
        float grade = 0.f;
        bool hasValue = false; // anti-spam
    };

    // -------- Runtime (dynamic, per-zone scheduler state) --------
    enum class Phase : uint8 { Idle = 0, FadeOut, FadeIn, Dwell };

    struct RepeatState
    {
        WeatherState lastPicked = WEATHER_STATE_FINE;
        uint32 repeats = 0; // consecutive times lastPicked was chosen
    };

    struct ZoneRuntime
    {
        // scheduling
        uint32 zoneId = 0;
        uint32 msAccumulator = 0;
        uint32 stepRemainingMs = 0;     // time left for current step
        uint32 phaseRemainingMs = 0;    // dwell only
        uint32 zoneOffsetMs = 0;        // stagger start

        // phase
        Phase phase = Phase::Idle;

        // current weather / fading grades
        WeatherState currentState = WEATHER_STATE_FINE;
        float currentGrade = 0.0f;      // actual grade last pushed

        // fade planning (out and in)
        int fadeOutStepsLeft = 0;
        float fadeOutStart = 0.0f;      // InternalRange.MAX of current state
        float fadeOutTarget = 0.0f;     // Internal MIN of next state (0% of next state's range)
        int fadeInStepsLeft = 0;
        float fadeInStart = 0.0f;       // InternalRange.MIN of next state
        float apexTarget = 0.0f;        // raw grade apex for next state

        // upcoming pick
        WeatherState nextState = WEATHER_STATE_FINE;

        // repeat control
        RepeatState rpt;

        // helper
        bool initialized = false;
    };

    // -------- Zone model (static config parsed from .conf) --------
    struct ZoneEffectEntry
    {
        WeatherState state = WEATHER_STATE_FINE;
        float weight = 0.0f;
        float minPct = 0.0f;   // 0..100
        float maxPct = 0.0f;   // 0..100
        uint32 dwellMinSec = 0;
        uint32 dwellMaxSec = 0;
    };

    struct ZoneDaypartConfig
    {
        std::vector<ZoneEffectEntry> entries; // entries with weight >= 0 (0 means disabled)
        bool HasAnyActive() const
        {
            for (auto const& e : entries) if (e.weight > 0.0f) return true;
            return false;
        }
    };

    // engine globals
    bool   g_EnableModule = true;
    bool   g_Debug = false;
    DayPartStarts g_Starts;
    std::string g_DayPartMode = "auto";
    std::string g_SeasonMode = "auto";
    uint32 g_IntervalSec = 10;
    uint32 g_RepeatMax = 2;
    float  g_FadeStepValue = 0.05f;
    uint32 g_FadeStepMinSec = 30;
    uint32 g_FadeStepMaxSec = 40;
    uint32 g_SchedulerSpreadMaxOffsetSec = 120;

    // Per-daypart per-WeatherState ranges (keyed by WeatherState value: 0,1,3,4,5,6,7,8,22,41,42,86)
    std::unordered_map<uint32, Range> g_StateRanges[(size_t)DayPart::COUNT];

    // per-zone last applied weather state and grade.
    std::unordered_map<uint32, LastApplied> g_LastApplied;

    // zoneId -> daypart index -> config
    std::unordered_map<uint32, ZoneDaypartConfig> g_ZoneModel[(size_t)DayPart::COUNT];

    // runtime per-zone (only for zones that have any config)
    std::unordered_map<uint32, ZoneRuntime> g_Runtime;
}

// ======================================
// Helpers (names)
// ======================================
static char const* WeatherStateName(WeatherState s)
{
    switch (s)
    {
    case WEATHER_STATE_FINE: return "fine";
    case WEATHER_STATE_FOG: return "fog";
    case WEATHER_STATE_LIGHT_RAIN: return "light_rain";
    case WEATHER_STATE_MEDIUM_RAIN: return "medium_rain";
    case WEATHER_STATE_HEAVY_RAIN: return "heavy_rain";
    case WEATHER_STATE_LIGHT_SNOW: return "light_snow";
    case WEATHER_STATE_MEDIUM_SNOW: return "medium_snow";
    case WEATHER_STATE_HEAVY_SNOW: return "heavy_snow";
    case WEATHER_STATE_LIGHT_SANDSTORM: return "light_sandstorm";
    case WEATHER_STATE_MEDIUM_SANDSTORM: return "medium_sandstorm";
    case WEATHER_STATE_HEAVY_SANDSTORM: return "heavy_sandstorm";
    case WEATHER_STATE_THUNDERS: return "thunders";
    case WEATHER_STATE_BLACKRAIN: return "blackrain";
    case WEATHER_STATE_BLACKSNOW: return "blacksnow";
    default: return "unknown";
    }
}

static char const* DayPartName(DayPart d)
{
    switch (d)
    {
    case DayPart::MORNING:   return "Morning";
    case DayPart::AFTERNOON: return "Afternoon";
    case DayPart::EVENING:   return "Evening";
    case DayPart::NIGHT:     return "Night";
    default:                 return "Unknown";
    }
}

static char const* DayPartTokenUpper(DayPart d)
{
    switch (d)
    {
    case DayPart::MORNING:   return "MORNING";
    case DayPart::AFTERNOON: return "AFTERNOON";
    case DayPart::EVENING:   return "EVENING";
    case DayPart::NIGHT:     return "NIGHT";
    default:                 return "UNKNOWN";
    }
}

static char const* ConfigStateToken(WeatherState s)
{
    switch (s)
    {
    case WEATHER_STATE_FINE:               return "Fine";
    case WEATHER_STATE_FOG:                return "Fog";
    case WEATHER_STATE_LIGHT_RAIN:         return "LightRain";
    case WEATHER_STATE_MEDIUM_RAIN:        return "MediumRain";
    case WEATHER_STATE_HEAVY_RAIN:         return "HeavyRain";
    case WEATHER_STATE_LIGHT_SNOW:         return "LightSnow";
    case WEATHER_STATE_MEDIUM_SNOW:        return "MediumSnow";
    case WEATHER_STATE_HEAVY_SNOW:         return "HeavySnow";
    case WEATHER_STATE_LIGHT_SANDSTORM:    return "LightSandstorm";
    case WEATHER_STATE_MEDIUM_SANDSTORM:   return "MediumSandstorm";
    case WEATHER_STATE_HEAVY_SANDSTORM:    return "HeavySandstorm";
    case WEATHER_STATE_THUNDERS:           return "Thunders";
    default:                               return "Unknown";
    }
}

static bool IsValidWeatherState(uint32 value)
{
    switch (value)
    {
    case WEATHER_STATE_FINE:
    case WEATHER_STATE_FOG:
    case WEATHER_STATE_LIGHT_RAIN:
    case WEATHER_STATE_MEDIUM_RAIN:
    case WEATHER_STATE_HEAVY_RAIN:
    case WEATHER_STATE_LIGHT_SNOW:
    case WEATHER_STATE_MEDIUM_SNOW:
    case WEATHER_STATE_HEAVY_SNOW:
    case WEATHER_STATE_LIGHT_SANDSTORM:
    case WEATHER_STATE_MEDIUM_SANDSTORM:
    case WEATHER_STATE_HEAVY_SANDSTORM:
    case WEATHER_STATE_THUNDERS:
        return true;
    default:
        return false;
    }
}

// Season naming helper
static char const* SeasonName(Season s)
{
    switch (s)
    {
    case Season::SPRING: return "Spring";
    case Season::SUMMER: return "Summer";
    case Season::AUTUMN: return "Autumn";
    case Season::WINTER: return "Winter";
    default:             return "Unknown";
    }
}

// ======================================
// Time helpers
// ======================================
static tm GetLocalTimeSafe()
{
    time_t now = GameTime::GetGameTime().count(); // unix seconds
    tm out{};
#if defined(_WIN32) || defined(_WIN64)
    localtime_s(&out, &now);
#else
    localtime_r(&now, &out);
#endif
    return out;
}

static int ParseHHMM(std::string const& s, int defMinutes)
{
    int h = 0, m = 0; char colon = 0;
    std::string t = s;
    t.erase(std::remove_if(t.begin(), t.end(), [](unsigned char c) { return std::isspace(c); }), t.end());

    if (std::sscanf(t.c_str(), "%d%c%d", &h, &colon, &m) == 3 && colon == ':' && h >= 0 && h < 24 && m >= 0 && m < 60)
    {
        return h * 60 + m;
    }

    if (std::sscanf(t.c_str(), "%d", &h) == 1 && h >= 0 && h < 24)
    {
        return h * 60;
    }

    return defMinutes;
}

static inline int ClampMinutes(int v)
{
    return std::clamp(v, 0, 23 * 60 + 59);
}

static void ValidateDayPartStarts()
{
    g_Starts.morning = ClampMinutes(g_Starts.morning);
    g_Starts.afternoon = std::max(ClampMinutes(g_Starts.afternoon), g_Starts.morning + 1);
    g_Starts.evening = std::max(ClampMinutes(g_Starts.evening), g_Starts.afternoon + 1);
    g_Starts.night = ClampMinutes(g_Starts.night); // wrap handled by GetCurrentDayPart()
}

// ======================================
// Intensity mapping helpers
// ======================================
static float ClampToCoreBounds(float g)
{
    if (g < 0.0f)
    {
        return kMinGrade;
    }
    if (g >= 1.0f)
    {
        return kMaxGrade;
    }

    return g;
}

static void LoadDayPartConfig()
{
    // Read modes (fallback to auto)
    g_DayPartMode = sConfigMgr->GetOption<std::string>("WeatherVibe.DayPart.Mode", "auto");
    g_SeasonMode = sConfigMgr->GetOption<std::string>("WeatherVibe.Season", "auto");

    // Only start times are configurable for boundaries
    g_Starts.morning = ParseHHMM(sConfigMgr->GetOption<std::string>("WeatherVibe.DayPart.MORNING.Start", "06:00"), 6 * 60);
    g_Starts.afternoon = ParseHHMM(sConfigMgr->GetOption<std::string>("WeatherVibe.DayPart.AFTERNOON.Start", "12:00"), 12 * 60);
    g_Starts.evening = ParseHHMM(sConfigMgr->GetOption<std::string>("WeatherVibe.DayPart.EVENING.Start", "18:00"), 18 * 60);
    g_Starts.night = ParseHHMM(sConfigMgr->GetOption<std::string>("WeatherVibe.DayPart.NIGHT.Start", "22:00"), 22 * 60);

    ValidateDayPartStarts();
}

static Range ParseRangePair(std::string const& key, Range def)
{
    std::string v = sConfigMgr->GetOption<std::string>(key, "");
    if (!v.empty())
    {
        float a = def.min, b = def.max;
        if (std::sscanf(v.c_str(), " %f , %f ", &a, &b) == 2)
        {
            if (b < a)
            {
                std::swap(a, b);
            }
            return { std::clamp(a,0.0f,1.0f), std::clamp(b,0.0f,1.0f) };
        }
    }

    return def;
}

static std::array<WeatherState, 12> const kAcceptedStates = {
    WEATHER_STATE_FINE,
    WEATHER_STATE_FOG,
    WEATHER_STATE_LIGHT_RAIN,
    WEATHER_STATE_MEDIUM_RAIN,
    WEATHER_STATE_HEAVY_RAIN,
    WEATHER_STATE_LIGHT_SNOW,
    WEATHER_STATE_MEDIUM_SNOW,
    WEATHER_STATE_HEAVY_SNOW,
    WEATHER_STATE_LIGHT_SANDSTORM,
    WEATHER_STATE_MEDIUM_SANDSTORM,
    WEATHER_STATE_HEAVY_SANDSTORM,
    WEATHER_STATE_THUNDERS
};

static void LoadStateRanges()
{
    for (size_t i = 0; i < (size_t)DayPart::COUNT; ++i)
    {
        g_StateRanges[i].clear();
    }

    auto makeKey = [](DayPart dp, WeatherState ws)
        {
            std::ostringstream oss;
            oss << "WeatherVibe.Intensity.InternalRange."
                << DayPartTokenUpper(dp) << "."
                << ConfigStateToken(ws);
            return oss.str();
        };

    // unified defaults for all states/dayparts
    Range def{ 0.30f, 1.00f };

    for (DayPart dp : { DayPart::MORNING, DayPart::AFTERNOON, DayPart::EVENING, DayPart::NIGHT })
    {
        for (WeatherState ws : kAcceptedStates)
        {
            g_StateRanges[(size_t)dp][(uint32)ws] = ParseRangePair(makeKey(dp, ws), def);
        }
    }
}

// Converts profile percent (0..1) to raw grade (per-WeatherState range)
static float MapPercentToRawGrade(DayPart dp, WeatherState state, float percent01)
{
    percent01 = std::clamp(percent01, 0.0f, 1.0f);
    auto const& table = g_StateRanges[(size_t)dp];
    auto it = table.find((uint32)state);
    Range r = (it != table.end()) ? it->second : Range{ 0.30f, 1.00f };

    return r.min + percent01 * (r.max - r.min);
}

// ======================================
// Day/Season helpers used by debug/show
// ======================================
static DayPart GetCurrentDayPart()
{
    // Honor config override if not auto
    std::string mode = g_DayPartMode;
    std::transform(mode.begin(), mode.end(), mode.begin(), [](unsigned char c) { return char(std::tolower(c)); });
    if (mode == "morning")
    {
        return DayPart::MORNING;
    }
    if (mode == "afternoon")
    {
        return DayPart::AFTERNOON;
    }
    if (mode == "evening")
    {
        return DayPart::EVENING;
    }
    if (mode == "night")
    {
        return DayPart::NIGHT;
    }

    // Auto: derive by time and configured boundaries
    tm lt = GetLocalTimeSafe();
    int minutes = lt.tm_hour * 60 + lt.tm_min;

    if (minutes >= g_Starts.night || minutes < g_Starts.morning)
    {
        return DayPart::NIGHT;
    }
    if (minutes >= g_Starts.evening)
    {
        return DayPart::EVENING;
    }
    if (minutes >= g_Starts.afternoon)
    {
        return DayPart::AFTERNOON;
    }

    return DayPart::MORNING;
}

static Season GetCurrentSeason()
{
    // Honor config override if not auto
    std::string m = g_SeasonMode;
    std::transform(m.begin(), m.end(), m.begin(), [](unsigned char c) { return char(std::tolower(c)); });
    if (m == "spring")
    {
        return Season::SPRING;
    }
    if (m == "summer")
    {
        return Season::SUMMER;
    }
    if (m == "autumn")
    {
        return Season::AUTUMN;
    }
    if (m == "winter")
    {
        return Season::WINTER;
    }

    // Auto: derive from day-of-year; anchor Spring around Mar 20 (~day 79)
    tm lt = GetLocalTimeSafe();
    int yday = lt.tm_yday; // 0..365
    uint32 seasonIndex = ((yday - 78 + 365) / 91) % 4; // 0:Spring,1:Summer,2:Autumn,3:Winter
    switch (seasonIndex)
    {
    default:
    case 0: return Season::SPRING;
    case 1: return Season::SUMMER;
    case 2: return Season::AUTUMN;
    case 3: return Season::WINTER;
    }
}

// ======================================
// Push weather to client and registers is lastApplied cache.
// ======================================
static bool PushWeatherToClient(uint32 zoneId, WeatherState state, float rawGrade)
{
    float normalizedGrade = ClampToCoreBounds(rawGrade);
    LastApplied& lastAppliedPtr = g_LastApplied[zoneId];

    WorldPackets::Misc::Weather weatherPackage(state, normalizedGrade);
    bool isApplied = sWorldSessionMgr->SendZoneMessage(zoneId, weatherPackage.Write());

    // Always record last-applied, even if no players were there to receive it.
    lastAppliedPtr.state = state;
    lastAppliedPtr.grade = normalizedGrade;
    lastAppliedPtr.hasValue = true;

    if (g_Debug)
    {
        DayPart d = GetCurrentDayPart();
        Season s = GetCurrentSeason();
        std::ostringstream zmsg;
        zmsg << "|cff00ff00WeatherVibe:|r [DEBUG] season=" << SeasonName(s)
            << " | day=" << DayPartName(d)
            << " | state=" << WeatherStateName(state)
            << " | grade=" << std::fixed << std::setprecision(2) << normalizedGrade
            << " | pushed=" << (isApplied ? "true" : "false");
        WorldSessionMgr::Instance()->SendZoneText(zoneId, zmsg.str().c_str());
    }

    return true; // treat as success even if no players
}

// ======================================
// Push weather to client with last applied of the zone, otherwise weatherState FINE.
// ======================================
static void PushLastAppliedWeatherToClient(uint32 zoneId, Player* player)
{
    // If we have a last-applied, use it.
    if (auto it = g_LastApplied.find(zoneId); it != g_LastApplied.end() && it->second.hasValue)
    {
        WorldPackets::Misc::Weather pkt(it->second.state, it->second.grade);
        player->SendDirectMessage(pkt.Write());
        return;
    }

    // If this zone is managed by the scheduler and already initialized, use its current state.
    if (auto rtIt = g_Runtime.find(zoneId); rtIt != g_Runtime.end())
    {
        ZoneRuntime const& rt = rtIt->second;
        if (rt.initialized)
        {
            WorldPackets::Misc::Weather pkt(rt.currentState, rt.currentGrade);
            player->SendDirectMessage(pkt.Write());
        }

        // else: scheduler will plan & push soon; don't touch current weather
        return;
    }

    // No profile, no cache: do nothing (leave core’s weather untouched).
}


// ======================================
// ============== ADD-ON ================
// Weighted zone model + fade scheduler
// ======================================
namespace
{
    // -------- RNG helpers --------
    static uint32 RandIn(uint32 a, uint32 b) // inclusive
    {
        if (a > b) std::swap(a, b);
        return urand(a, b);
    }
    static float RandUnit() // [0,1]
    {
        return float(urand(0, 10000)) / 10000.0f;
    }

    // -------- Internals --------
    static WeatherState AllStatesList[] = {
        WEATHER_STATE_FINE, WEATHER_STATE_FOG,
        WEATHER_STATE_LIGHT_RAIN, WEATHER_STATE_MEDIUM_RAIN, WEATHER_STATE_HEAVY_RAIN,
        WEATHER_STATE_LIGHT_SNOW, WEATHER_STATE_MEDIUM_SNOW, WEATHER_STATE_HEAVY_SNOW,
        WEATHER_STATE_LIGHT_SANDSTORM, WEATHER_STATE_MEDIUM_SANDSTORM, WEATHER_STATE_HEAVY_SANDSTORM,
        WEATHER_STATE_THUNDERS
    };

    static char const* MakeZoneKey(uint32 zoneId, DayPart dp, WeatherState st, char* buf, size_t n)
    {
        // WeatherVibe.Zone.<zone>.<DAYPART>.<State> = <weight> <min%> <max%> <minDwell> <maxDwell>
        std::snprintf(buf, n, "WeatherVibe.Zone.%u.%s.%s",
            zoneId, DayPartTokenUpper(dp), ConfigStateToken(st));
        return buf;
    }

    static bool ParseZoneEntry(char const* raw, ZoneEffectEntry& out)
    {
        // Format: <weight> <minPct> <maxPct> <minDwell> <maxDwell>
        if (!raw || !*raw) return false;
        float w = 0.0f, pmin = 0.0f, pmax = 0.0f; uint32 dmin = 0, dmax = 0;
        int matched = std::sscanf(raw, " %f %f %f %u %u ", &w, &pmin, &pmax, &dmin, &dmax);
        if (matched != 5) return false;
        if (pmax < pmin) std::swap(pmin, pmax);
        pmin = std::clamp(pmin, 0.0f, 100.0f);
        pmax = std::clamp(pmax, 0.0f, 100.0f);
        out.weight = w;
        out.minPct = pmin;
        out.maxPct = pmax;
        out.dwellMinSec = dmin;
        out.dwellMaxSec = std::max(dmax, dmin);
        out.dwellMinSec = std::min(out.dwellMinSec, 24u * 3600u);
        out.dwellMaxSec = std::min(out.dwellMaxSec, 24u * 3600u);
        return true;
    }

    static Range GetRange(DayPart dp, WeatherState st)
    {
        auto const& t = g_StateRanges[(size_t)dp];
        auto it = t.find((uint32)st);
        if (it != t.end()) return it->second;
        return Range{ 0.30f, 0.90f };
    }

    static float ApexFromPct(DayPart dp, WeatherState st, float pct01)
    {
        return MapPercentToRawGrade(dp, st, pct01);
    }

    static DayPart CurrentDayPart()
    {
        return GetCurrentDayPart();
    }

    static void LoadEngineGlobals()
    {
        g_IntervalSec = sConfigMgr->GetOption<uint32>("WeatherVibe.IntervalSec", 10);
        g_RepeatMax = sConfigMgr->GetOption<uint32>("WeatherVibe.Zone.Repeat.Max", 2);
        std::string step = sConfigMgr->GetOption<std::string>("WeatherVibe.Fade.StepValue", "0.05");
        g_FadeStepValue = std::max(0.0005f, std::min(0.5f, float(std::atof(step.c_str())))); // safety clamp
        g_FadeStepMinSec = sConfigMgr->GetOption<uint32>("WeatherVibe.Fade.StepDuration.Min", 30);
        g_FadeStepMaxSec = std::max(g_FadeStepMinSec, sConfigMgr->GetOption<uint32>("WeatherVibe.Fade.StepDuration.Max", 40));
        g_SchedulerSpreadMaxOffsetSec = sConfigMgr->GetOption<uint32>("WeatherVibe.Scheduler.Spread.MaxOffsetSec", 120);
    }

    static ZoneDaypartConfig const* GetZoneDaypart(uint32 zoneId, DayPart dp)
    {
        auto it = g_ZoneModel[(size_t)dp].find(zoneId);
        if (it == g_ZoneModel[(size_t)dp].end()) return nullptr;
        return &it->second;
    }

    static void LoadZoneModelFor(uint32 zoneId)
    {
        for (DayPart dp : { DayPart::MORNING, DayPart::AFTERNOON, DayPart::EVENING, DayPart::NIGHT })
        {
            ZoneDaypartConfig zdc;
            for (WeatherState st : AllStatesList)
            {
                char key[256];
                auto* k = MakeZoneKey(zoneId, dp, st, key, sizeof(key));
                std::string raw = sConfigMgr->GetOption<std::string>(k, "");
                if (raw.empty()) continue;

                ZoneEffectEntry e;
                e.state = st;
                if (ParseZoneEntry(raw.c_str(), e))
                {
                    zdc.entries.push_back(e);
                }
            }
            if (!zdc.entries.empty())
            {
                g_ZoneModel[(size_t)dp][zoneId] = std::move(zdc);
            }
        }
    }

    static std::vector<uint32> ParseZoneIdList(std::string const& csv)
    {
        std::vector<uint32> out;
        uint32 cur = 0; bool have = false;
        for (char c : csv)
        {
            if (std::isdigit((unsigned char)c))
            {
                cur = (cur * 10u) + uint32(c - '0');
                have = true;
            }
            else
            {
                if (have) { out.push_back(cur); cur = 0; have = false; }
            }
        }
        if (have) out.push_back(cur);
        // de-dup
        std::sort(out.begin(), out.end());
        out.erase(std::unique(out.begin(), out.end()), out.end());
        return out;
    }

    static bool ZoneHasProfile(uint32 zoneId)
    {
        for (size_t i = 0; i < (size_t)DayPart::COUNT; ++i)
            if (g_ZoneModel[i].find(zoneId) != g_ZoneModel[i].end())
                return true;
        return false;
    }

    static void LoadZoneModels()
    {
        // Clear tables
        for (size_t i = 0; i < (size_t)DayPart::COUNT; ++i) g_ZoneModel[i].clear();
        g_Runtime.clear();

        // Read list from config (CSV of zone IDs)
        // e.g. WeatherVibe.Zone.List = 1,3,4,8,10,11,12,14,15,16,17,25,28,33,36,38,40,41,...,14288
        std::string listCsv = sConfigMgr->GetOption<std::string>("WeatherVibe.Zone.List", "");
        auto ids = ParseZoneIdList(listCsv);

        // Load each zone that appears in the list
        for (uint32 zid : ids)
        {
            LoadZoneModelFor(zid);

            // Seed runtime for any daypart that ended up with entries
            bool hasAny = false;
            for (size_t i = 0; i < (size_t)DayPart::COUNT; ++i)
                hasAny |= (g_ZoneModel[i].find(zid) != g_ZoneModel[i].end());

            if (hasAny && !g_Runtime.count(zid))
            {
                ZoneRuntime rt;
                rt.zoneId = zid;
                rt.zoneOffsetMs = RandIn(0, g_SchedulerSpreadMaxOffsetSec) * 1000;
                g_Runtime[zid] = rt;
            }
        }
    }

    static WeatherState WeightedPick(struct ZoneDaypartConfig const& cfg, struct RepeatState const& rpt, uint32 repeatMax)
    {
        // Build list with optional exclusion when repeatMax reached
        struct Item { WeatherState st; float w; ZoneEffectEntry const* e; };
        std::vector<Item> pool;
        pool.reserve(cfg.entries.size());
        for (auto const& e : cfg.entries)
        {
            if (e.weight <= 0.0f) continue;
            if (rpt.repeats >= repeatMax && e.state == rpt.lastPicked)
            {
                continue; // exclude this state for this roll
            }
            pool.push_back({ e.state, e.weight, &e });
        }
        if (pool.empty())
        {
            if (pool.empty())
            {
                // No valid candidates — keep last state (don’t force Fine)
                return rpt.lastPicked;
            }
        }

        float sum = 0.0f;
        for (auto const& it : pool) sum += it.w;
        float r = RandUnit() * sum;
        for (auto const& it : pool)
        {
            if ((r -= it.w) <= 0.0f)
                return it.st;
        }
        return pool.back().st;
    }

    static ZoneEffectEntry const* FindEntry(ZoneDaypartConfig const& cfg, WeatherState st)
    {
        for (auto const& e : cfg.entries) if (e.state == st) return &e;
        return nullptr;
    }

    static uint32 RandDuration(uint32 minSec, uint32 maxSec)
    {
        return RandIn(minSec, maxSec) * 1000;
    }

    static void PlanNewEffect(ZoneRuntime& rt)
    {
        constexpr float kEps = 1e-4f;

        DayPart dp = CurrentDayPart();
        ZoneDaypartConfig const* cfg = GetZoneDaypart(rt.zoneId, dp);

        // No profile for this daypart → leave weather untouched; try again later.
        if (!cfg || !cfg->HasAnyActive())
        {
            rt.phase = Phase::Idle;
            return;
        }

        // Pick next state with repeat control.
        WeatherState pick = WeightedPick(*cfg, rt.rpt, g_RepeatMax);
        ZoneEffectEntry const* entry = FindEntry(*cfg, pick);
        if (!entry)
        {
            // Nothing valid to apply now — leave as-is.
            rt.phase = Phase::Idle;
            return;
        }

        // Roll an apex within the zone's % band and map to raw using the global InternalRange.
        float pct01 = std::clamp((entry->minPct + (entry->maxPct - entry->minPct) * RandUnit()) / 100.0f, 0.0f, 1.0f);
        float apex = ApexFromPct(dp, pick, pct01);

        Range newRange = GetRange(dp, pick);
        Range curRange = GetRange(dp, rt.currentState);

        // Record targets for the upcoming transition.
        rt.nextState = pick;
        rt.apexTarget = apex;
        rt.fadeInStart = newRange.min;   // 0% point of the new state's internal range

        // ---------- First run (no previous state pushed) ----------
        if (!rt.initialized)
        {
            // Initialize: push the picked state at MIN so clients see the correct effect immediately.
            rt.currentState = pick;
            rt.currentGrade = ClampToCoreBounds(newRange.min);
            PushWeatherToClient(rt.zoneId, rt.currentState, rt.currentGrade);

            // Plan only FadeIn to the apex (no FadeOut on first run).
            float inDelta = std::max(0.0f, rt.apexTarget - rt.currentGrade);
            rt.fadeOutStepsLeft = 0;
            rt.fadeInStepsLeft = (inDelta <= 0.0f) ? 0 : int(std::ceil(inDelta / g_FadeStepValue));

            if (rt.fadeInStepsLeft > 0)
            {
                rt.phase = Phase::FadeIn;
                rt.stepRemainingMs = RandDuration(g_FadeStepMinSec, g_FadeStepMaxSec);
            }
            else
            {
                rt.phase = Phase::Dwell;
                rt.phaseRemainingMs = RandDuration(entry->dwellMinSec, entry->dwellMaxSec);
            }

            rt.rpt.lastPicked = pick;
            rt.rpt.repeats = 1;
            rt.initialized = true;
            return;
        }

        // ---------- Subsequent runs ----------
        bool sameState = (pick == rt.currentState);

        // Case 1: same state, apex ABOVE current → gentle fade up (no drop to MIN).
        if (sameState && rt.apexTarget > rt.currentGrade + kEps)
        {
            // Start from current (but AdvanceFadeIn will enforce >= MIN).
            float inDelta = std::max(0.0f, rt.apexTarget - std::max(rt.currentGrade, newRange.min));
            rt.fadeOutStepsLeft = 0;
            rt.fadeInStepsLeft = (inDelta <= 0.0f) ? 0 : int(std::ceil(inDelta / g_FadeStepValue));

            if (rt.fadeInStepsLeft > 0)
            {
                rt.phase = Phase::FadeIn;
                rt.stepRemainingMs = RandDuration(g_FadeStepMinSec, g_FadeStepMaxSec);
            }
            else
            {
                rt.phase = Phase::Dwell;
                rt.phaseRemainingMs = RandDuration(entry->dwellMinSec, entry->dwellMaxSec);
            }
        }
        // Case 2: same state, apex BELOW current → gentle fade down within the same state.
        else if (sameState && rt.apexTarget < rt.currentGrade - kEps)
        {
            rt.fadeOutStart = rt.currentGrade;   // fade down from current grade
            rt.fadeOutTarget = rt.apexTarget;     // to the new apex (same state)
            float outDelta = std::max(0.0f, rt.fadeOutStart - rt.fadeOutTarget);
            rt.fadeOutStepsLeft = (outDelta <= 0.0f) ? 0 : int(std::ceil(outDelta / g_FadeStepValue));
            rt.fadeInStepsLeft = 0;

            if (rt.fadeOutStepsLeft > 0)
            {
                rt.phase = Phase::FadeOut;
                rt.stepRemainingMs = RandDuration(g_FadeStepMinSec, g_FadeStepMaxSec);
            }
            else
            {
                rt.phase = Phase::Dwell;
                rt.phaseRemainingMs = RandDuration(entry->dwellMinSec, entry->dwellMaxSec);
            }
        }
        // Case 3: different state → classic fade-out (old MAX → new MIN) then fade-in to apex.
        else
        {
            rt.fadeOutStart = curRange.max;      // per design: fade-out starts at current state's MAX
            rt.fadeOutTarget = newRange.min;      // and goes down to new state's MIN
            float outDelta = std::max(0.0f, rt.fadeOutStart - rt.fadeOutTarget);
            rt.fadeOutStepsLeft = (outDelta <= 0.0f) ? 0 : int(std::ceil(outDelta / g_FadeStepValue));

            float inDelta = std::max(0.0f, rt.apexTarget - newRange.min);
            rt.fadeInStepsLeft = (inDelta <= 0.0f) ? 0 : int(std::ceil(inDelta / g_FadeStepValue));

            if (rt.fadeOutStepsLeft > 0)
            {
                rt.phase = Phase::FadeOut;
                rt.stepRemainingMs = RandDuration(g_FadeStepMinSec, g_FadeStepMaxSec);
            }
            else if (rt.fadeInStepsLeft > 0)
            {
                rt.phase = Phase::FadeIn;
                rt.stepRemainingMs = RandDuration(g_FadeStepMinSec, g_FadeStepMaxSec);
            }
            else
            {
                rt.phase = Phase::Dwell;
                rt.phaseRemainingMs = RandDuration(entry->dwellMinSec, entry->dwellMaxSec);
            }
        }

        // Update repeat tracking.
        if (pick == rt.rpt.lastPicked) ++rt.rpt.repeats;
        else { rt.rpt.lastPicked = pick; rt.rpt.repeats = 1; }
    }


    static void AdvanceFadeOut(ZoneRuntime& rt)
    {
        // If we’re already done fading out, jump straight into fade-in.
        if (rt.fadeOutStepsLeft <= 0)
        {
            if (rt.fadeInStepsLeft > 0)
            {
                // Switch state now and push a baseline at MIN so clients don’t sit on the old state
                rt.currentState = rt.nextState;
                rt.currentGrade = ClampToCoreBounds(rt.fadeInStart); // new state's MIN
                PushWeatherToClient(rt.zoneId, rt.currentState, rt.currentGrade);

                rt.phase = Phase::FadeIn;
                rt.stepRemainingMs = RandDuration(g_FadeStepMinSec, g_FadeStepMaxSec);
            }
            else
            {
                // No fade-in needed; go dwell right away
                rt.phase = Phase::Dwell;
                rt.stepRemainingMs = 0;
            }
            return;
        }

        // Do one fade-out step (still pushing the OLD state)
        float next = std::max(rt.fadeOutTarget, rt.currentGrade - g_FadeStepValue);
        rt.currentGrade = ClampToCoreBounds(next);
        PushWeatherToClient(rt.zoneId, rt.currentState, rt.currentGrade);

        rt.fadeOutStepsLeft--;
        rt.stepRemainingMs = RandDuration(g_FadeStepMinSec, g_FadeStepMaxSec);

        if (rt.fadeOutStepsLeft <= 0)
        {
            if (rt.fadeInStepsLeft > 0)
            {
                // Immediately flip to the NEW state at MIN and begin fade-in next tick
                rt.currentState = rt.nextState;
                rt.currentGrade = ClampToCoreBounds(rt.fadeInStart);
                PushWeatherToClient(rt.zoneId, rt.currentState, rt.currentGrade);

                rt.phase = Phase::FadeIn;
                rt.stepRemainingMs = RandDuration(g_FadeStepMinSec, g_FadeStepMaxSec);
            }
            else
            {
                rt.phase = Phase::Dwell;
                rt.stepRemainingMs = 0;
            }
        }
    }

    static void AdvanceFadeIn(ZoneRuntime& rt)
    {
        if (rt.fadeInStepsLeft <= 0)
        {
            // ... (unchanged)
            return;
        }

        // Ensure we start from MIN even if currentGrade came from the last push
        float base = std::max(rt.currentGrade, rt.fadeInStart);
        float next = std::min(rt.apexTarget, base + g_FadeStepValue);

        rt.currentGrade = ClampToCoreBounds(next);
        PushWeatherToClient(rt.zoneId, rt.currentState /* already new */, rt.currentGrade);

        rt.fadeInStepsLeft--;
        rt.stepRemainingMs = (rt.fadeInStepsLeft > 0)
            ? RandDuration(g_FadeStepMinSec, g_FadeStepMaxSec)
            : 0;

        if (rt.fadeInStepsLeft <= 0)
        {
            // Land exactly on apex and enter dwell
            rt.currentGrade = ClampToCoreBounds(rt.apexTarget);
            PushWeatherToClient(rt.zoneId, rt.currentState, rt.currentGrade);

            DayPart dp = CurrentDayPart();
            auto* cfg = GetZoneDaypart(rt.zoneId, dp);
            if (auto* entry = cfg ? FindEntry(*cfg, rt.currentState) : nullptr)
                rt.phaseRemainingMs = RandDuration(entry->dwellMinSec, entry->dwellMaxSec);
            else
                rt.phaseRemainingMs = 5000;

            rt.phase = Phase::Dwell;
        }
    }


    static void AdvanceDwell(ZoneRuntime& rt, uint32 diffMs)
    {
        if (rt.phaseRemainingMs > diffMs) { rt.phaseRemainingMs -= diffMs; return; }
        // dwell finished → plan a new effect
        rt.phaseRemainingMs = 0;
        PlanNewEffect(rt);
    }

    static void ResetRepeatsOnContextChange(ZoneRuntime& rt, DayPart oldDp, DayPart newDp)
    {
        if (oldDp != newDp)
        {
            rt.rpt.repeats = 0;
            rt.rpt.lastPicked = WEATHER_STATE_FINE;
        }
    }

    // Called by world update
    static void SchedulerUpdate(uint32 diffMs)
    {
        if (!g_EnableModule) return;

        static DayPart s_LastDp = CurrentDayPart();

        DayPart currentDp = CurrentDayPart();
        for (auto& kv : g_Runtime)
        {
            ZoneRuntime& rt = kv.second;

            // Stagger start
            if (rt.zoneOffsetMs > 0)
            {
                uint32 consume = std::min(rt.zoneOffsetMs, diffMs);
                rt.zoneOffsetMs -= consume;
                if (rt.zoneOffsetMs > 0) continue;
            }

            // Reset repeat counters on daypart change
            ResetRepeatsOnContextChange(rt, s_LastDp, currentDp);

            rt.msAccumulator += diffMs;
            uint32 intervalMs = g_IntervalSec * 1000;
            if (intervalMs == 0) intervalMs = 1000;

            // Step only on beat or when step timers expire
            while (rt.msAccumulator >= intervalMs)
            {
                rt.msAccumulator -= intervalMs;

                // step timers (fade step pacing)
                if (rt.stepRemainingMs > 0)
                {
                    if (rt.stepRemainingMs > intervalMs) rt.stepRemainingMs -= intervalMs;
                    else rt.stepRemainingMs = 0;
                }

                if (rt.phase == Phase::Idle)
                {
                    PlanNewEffect(rt);
                }
                else if (rt.phase == Phase::FadeOut)
                {
                    if (rt.stepRemainingMs == 0) AdvanceFadeOut(rt);
                }
                else if (rt.phase == Phase::FadeIn)
                {
                    if (rt.stepRemainingMs == 0) AdvanceFadeIn(rt);
                }
                else if (rt.phase == Phase::Dwell)
                {
                    AdvanceDwell(rt, intervalMs);
                }
            }
        }

        s_LastDp = currentDp;
    }

    // -------- Show helper (augment .wvibe show) --------
    static std::string RuntimeLine(uint32 zoneId)
    {
        auto it = g_Runtime.find(zoneId);
        if (it == g_Runtime.end()) return std::string{};
        ZoneRuntime const& rt = it->second;

        auto phaseName = [](Phase p)
            {
                switch (p)
                {
                case Phase::Idle: return "idle";
                case Phase::FadeOut: return "fade_out";
                case Phase::FadeIn: return "fade_in";
                case Phase::Dwell: return "dwell";
                }
                return "unknown";
            };

        std::ostringstream o;
        o << " | phase=" << phaseName(rt.phase);

        if (rt.phase == Phase::FadeOut || rt.phase == Phase::FadeIn)
        {
            o << " step_remaining=" << (rt.stepRemainingMs / 1000) << "s";
            if (rt.phase == Phase::FadeOut) o << " steps_left=" << rt.fadeOutStepsLeft;
            if (rt.phase == Phase::FadeIn)  o << " steps_left=" << rt.fadeInStepsLeft;
        }
        else if (rt.phase == Phase::Dwell)
        {
            o << " remaining=" << (rt.phaseRemainingMs / 1000) << "s";
        }

        o << " repeats=" << rt.rpt.repeats << "/" << g_RepeatMax;
        return o.str();
    }

    // -------- Public entry points used by existing code --------
    static void WeatherVibe_LoadAllConfig()
    {
        LoadDayPartConfig();
        LoadEngineGlobals();
        LoadStateRanges();    // existing internal ranges
        LoadZoneModels();     // new zone model
    }
} // end anon namespace

// ======================================
// Commands
// ======================================

// .wvibe set <zoneId> <state:uint> <percentage:0..100>
static bool HandleCommandPercent(ChatHandler* handler, uint32 zoneId, uint32 stateVal, float percentage)
{
    if (!g_EnableModule)
    {
        handler->SendSysMessage("|cff00ff00WeatherVibe:|r Module is disabled in config.");
        return false;
    }
    if (!IsValidWeatherState(stateVal))
    {
        handler->SendSysMessage("|cff00ff00WeatherVibe:|r Invalid state. Examples: 0=Fine, 1=Fog, 3=LightRain, 4=MediumRain, 5=HeavyRain, 6=LightSnow, 7=MediumSnow, 8=HeavySnow, 22=LightSandstorm, 41=MediumSandstorm, 42=HeavySandstorm, 86=Thunders.");
        handler->SendSysMessage("Usage: .wvibe set <zoneId> <state:uint> <percentage:0..100>");
        return false;
    }

    float pct01 = std::clamp(percentage, 0.0f, 100.0f) / 100.0f;
    DayPart dp = GetCurrentDayPart();
    float raw = MapPercentToRawGrade(dp, static_cast<WeatherState>(stateVal), pct01);

    return PushWeatherToClient(zoneId, static_cast<WeatherState>(stateVal), raw);
}

// .wvibe setRaw <zoneId> <state:uint> <raw:0..1>
static bool HandleCommandRaw(ChatHandler* handler, uint32 zoneId, uint32 stateVal, float grade)
{
    if (!g_EnableModule)
    {
        handler->SendSysMessage("|cff00ff00WeatherVibe:|r Module is disabled in config.");
        return false;
    }
    if (!IsValidWeatherState(stateVal))
    {
        handler->SendSysMessage("Usage: .wvibe setRaw <zoneId> <state:uint> <raw:0..1>");
        return false;
    }

    float raw = std::clamp(grade, 0.0f, 1.0f);
    return PushWeatherToClient(zoneId, static_cast<WeatherState>(stateVal), raw);
}

class WeatherVibe_CommandScript : public CommandScript
{
public:
    WeatherVibe_CommandScript() : CommandScript("WeatherVibe_CommandScript") {}

    // ====== REPLACED: HandleWvibeReload ======
    static bool HandleWvibeReload(ChatHandler* handler)
    {
        if (!g_EnableModule)
        {
            handler->SendSysMessage("|cff00ff00WeatherVibe:|r Is disabled (WeatherVibe.Enable = 0).");
            return false;
        }

        WeatherVibe_LoadAllConfig();

        handler->SendSysMessage("|cff00ff00WeatherVibe:|r Reloaded (ranges/dayparts/zone-model).");
        return true;
    }

    // ====== REPLACED: HandleWvibeShow (augmented) ======
    static bool HandleWvibeShow(ChatHandler* handler)
    {
        if (!g_EnableModule)
        {
            handler->SendSysMessage("|cff00ff00WeatherVibe:|r Is disabled (WeatherVibe.Enable = 0).");
            return false;
        }

        if (g_LastApplied.empty() && g_Runtime.empty())
        {
            handler->SendSysMessage("|cff00ff00WeatherVibe:|r No data yet. Use .wvibe set/setRaw or wait for scheduler.");
            return true;
        }

        DayPart d = GetCurrentDayPart();
        Season s = GetCurrentSeason();

        std::ostringstream oss;
        oss << "|cff00ff00WeatherVibe:|r show | season=" << SeasonName(s) << " | daypart=" << DayPartName(d) << "\n";

        // First: last-applied (legacy)
        for (auto const& kv : g_LastApplied)
        {
            uint32 zoneId = kv.first;
            LastApplied const& la = kv.second;
            oss << "zone " << zoneId
                << " -> last state=" << WeatherStateName(la.state)
                << " raw=" << std::fixed << std::setprecision(2) << la.grade;

            std::string extra = RuntimeLine(zoneId);
            if (!extra.empty()) oss << extra;
            oss << "\n";
        }

        // Also show zones that are managed but not yet in last-applied
        for (auto const& kv : g_Runtime)
        {
            if (g_LastApplied.count(kv.first)) continue;
            oss << "zone " << kv.first
                << " -> last state=unknown raw=0.00";

            std::string extra = RuntimeLine(kv.first);
            if (!extra.empty()) oss << extra;
            oss << "\n";
        }

        handler->SendSysMessage(oss.str().c_str());
        return true;
    }

    static bool HandleWvibeSet(ChatHandler* handler, uint32 zoneId, uint32 stateVal, float percentage)
    {
        return HandleCommandPercent(handler, zoneId, stateVal, percentage);
    }

    static bool HandleWvibeSetRaw(ChatHandler* handler, uint32 zoneId, uint32 stateVal, float rawGrade)
    {
        return HandleCommandRaw(handler, zoneId, stateVal, rawGrade);
    }

    ChatCommandTable GetCommands() const override
    {
        static ChatCommandTable wvibeSet =
        {
            { "set",    HandleWvibeSet,    SEC_ADMINISTRATOR, Console::Yes },
            { "setRaw", HandleWvibeSetRaw, SEC_ADMINISTRATOR, Console::Yes },
            { "reload", HandleWvibeReload, SEC_ADMINISTRATOR, Console::Yes },
            { "show",   HandleWvibeShow,   SEC_ADMINISTRATOR, Console::Yes },
        };
        static ChatCommandTable root =
        {
            { "wvibe", wvibeSet }
        };
        return root;
    }
};

// ==========================
// Player hooks @see PlayerScript.h
// ==========================
class WeatherVibe_PlayerScript : public PlayerScript
{
public:
    WeatherVibe_PlayerScript() : PlayerScript("WeatherVibe_PlayerScript") {}

    void OnPlayerLogin(Player* player) override
    {
        if (!g_EnableModule)
        {
            return;
        }

        ChatHandler(player->GetSession()).SendSysMessage("|cff00ff00WeatherVibe:|r enabled");

        // push weather to client with last applied of the zone, otherwise weatherState FINE.
        PushLastAppliedWeatherToClient(player->GetZoneId(), player);

    }

    void OnPlayerUpdateZone(Player* player, uint32 newZone, uint32 /*newArea*/) override
    {
        if (!g_EnableModule)
        {
            return;
        }

        // push weather to client with last applied of the zone, otherwise weatherState FINE.
        PushLastAppliedWeatherToClient(newZone, player);
    }
};

// ==========================
// World hooks @see WorldScript.h (foundation)
// ==========================
class WeatherVibe_WorldScript : public WorldScript
{
public:
    WeatherVibe_WorldScript() : WorldScript("WeatherVibe_WorldScript") {}

    void OnStartup() override
    {
        g_EnableModule = sConfigMgr->GetOption<bool>("WeatherVibe.Enable", true);
        if (!g_EnableModule)
        {
            LOG_INFO("server.loading", "[WeatherVibe] disabled by config");
            return;
        }

        g_Debug = sConfigMgr->GetOption<uint32>("WeatherVibe.Debug", 0) != 0;

        WeatherVibe_LoadAllConfig();
        g_LastApplied.clear();

        // Immediately select first effect per zone
        for (auto& kv : g_Runtime)
        {
            ZoneRuntime& rt = kv.second;
            if (ZoneHasProfile(rt.zoneId))
            {
                // Roll and push the first effect now (respects ranges; starts at MIN of the picked state)
                PlanNewEffect(rt);
            }
        }

        LOG_INFO("server.loading", "[WeatherVibe] started (packet mode, per-state ranges, scheduler)");
    }
};

// ==========================
// World hooks (scheduler ticker)
// ==========================
class WeatherVibe_SchedulerWorldScript : public WorldScript
{
public:
    WeatherVibe_SchedulerWorldScript() : WorldScript("WeatherVibe_SchedulerWorldScript") {}

    void OnStartup() override
    {
        // already loaded by foundation world script; nothing extra required here.
    }

    void OnUpdate(uint32 diff) override
    {
        if (!g_EnableModule) return;
        SchedulerUpdate(diff);
    }
};

// ==================
// Module entry point
// ==================
void Addmod_weather_vibeScripts()
{
    new WeatherVibe_CommandScript();
    new WeatherVibe_PlayerScript();
    new WeatherVibe_WorldScript();
    new WeatherVibe_SchedulerWorldScript(); // added
}
