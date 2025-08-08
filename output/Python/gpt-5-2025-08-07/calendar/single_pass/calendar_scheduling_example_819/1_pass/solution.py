from typing import List, Tuple, Dict

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time_str(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def subtract_intervals(base: List[Tuple[int, int]], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    busy = merge_intervals(busy)
    result = []
    for bs, be in base:
        cur_start = bs
        for s, e in busy:
            if e <= cur_start or s >= be:
                continue
            if s > cur_start:
                result.append((cur_start, min(s, be)))
            cur_start = max(cur_start, e)
            if cur_start >= be:
                break
        if cur_start < be:
            result.append((cur_start, be))
    return result

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    result = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            result.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return result

# Configuration
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
work_hours = [(work_start, work_end)]
duration = 30  # minutes
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Participants' schedules
schedules: Dict[str, Dict[str, List[Tuple[int, int]]]] = {
    "Julie": {day: [] for day in days},  # No meetings all week
    "Ruth": {
        "Monday": [(work_start, work_end)],
        "Tuesday": [(work_start, work_end)],
        "Wednesday": [(work_start, work_end)],
        "Thursday": [
            (to_minutes("09:00"), to_minutes("11:00")),
            (to_minutes("11:30"), to_minutes("14:30")),
            (to_minutes("15:00"), to_minutes("17:00")),
        ],
    },
}

# Preference: Julie would like to avoid Thursday meetings before 11:30
preference_thresholds = {
    "Thursday": to_minutes("11:30")
}

def find_slot(respect_preferences: bool = True):
    for day in days:
        # Start with work hours as the base availability
        common_free = work_hours[:]
        # Intersect free time for each participant
        for person, person_sched in schedules.items():
            busy_today = person_sched.get(day, [])
            free_today = subtract_intervals(work_hours, busy_today)
            common_free = intersect_intervals(common_free, free_today)
            if not common_free:
                break
        if not common_free:
            continue

        pref_min = preference_thresholds.get(day) if respect_preferences else None

        # Find earliest slot that fits the duration (respecting preference if applicable)
        for s, e in common_free:
            start_candidate = max(s, pref_min) if pref_min is not None else s
            if start_candidate + duration <= e:
                return day, start_candidate, start_candidate + duration
    return None

# Try honoring preferences first, then fallback if needed
result = find_slot(respect_preferences=True) or find_slot(respect_preferences=False)

if not result:
    raise SystemExit("No feasible meeting time found.")

day, start_min, end_min = result

print(day)
print(f"{{{to_time_str(start_min)}:{to_time_str(end_min)}}}")