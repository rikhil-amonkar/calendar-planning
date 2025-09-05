from typing import List, Tuple

# Utility functions
def to_minutes(time_str: str) -> int:
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

def to_hhmm(minutes: int) -> str:
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def subtract_intervals(base: List[Tuple[int, int]], remove: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    # Subtract 'remove' intervals from 'base' intervals
    result = []
    for bs, be in base:
        temp = [(bs, be)]
        for rs, re in remove:
            new_temp = []
            for ts, te in temp:
                if re <= ts or rs >= te:  # no overlap
                    new_temp.append((ts, te))
                else:
                    if rs > ts:
                        new_temp.append((ts, rs))
                    if re < te:
                        new_temp.append((re, te))
            temp = new_temp
        result.extend(temp)
    # Merge any adjacent intervals
    result.sort()
    merged = []
    for s, e in result:
        if not merged or s > merged[-1][1]:
            merged.append([s, e])
        else:
            merged[-1][1] = max(merged[-1][1], e)
    return [(s, e) for s, e in merged]

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    out = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            out.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return out

def find_slot(free: List[Tuple[int, int]], duration: int) -> Tuple[int, int] | None:
    for s, e in free:
        if e - s >= duration:
            return (s, s + duration)
    return None

# Problem setup (Monday schedules)
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
work_window = [(work_start, work_end)]
duration = 30  # minutes

# Existing busy schedules
eric_busy = [
    (to_minutes("12:00"), to_minutes("13:00")),
    (to_minutes("14:00"), to_minutes("15:00")),
]

henry_busy = [
    (to_minutes("09:30"), to_minutes("10:00")),
    (to_minutes("10:30"), to_minutes("11:00")),
    (to_minutes("11:30"), to_minutes("12:30")),
    (to_minutes("13:00"), to_minutes("13:30")),
    (to_minutes("14:30"), to_minutes("15:00")),
    (to_minutes("16:00"), to_minutes("17:00")),
]

# Preference: Henry would rather not meet after 10:00 on Monday
preference_end = to_minutes("10:00")
preferred_window = [(work_start, min(preference_end, work_end))]

# Compute free intervals within work hours
eric_free = subtract_intervals(work_window, eric_busy)
henry_free = subtract_intervals(work_window, henry_busy)

# Common free intervals
common_free = intersect_intervals(eric_free, henry_free)

# Try preferred window first
preferred_common = intersect_intervals(common_free, preferred_window)
slot = find_slot(preferred_common, duration)

# Fallback to any time within work hours if needed
if not slot:
    slot = find_slot(common_free, duration)

# Output
if slot:
    start_str = to_hhmm(slot[0])
    end_str = to_hhmm(slot[1])
    print(day)
    print(f"{start_str}:{end_str}")
    print(f"{{{start_str}:{end_str}}}")
else:
    # This should not happen per problem statement (a solution exists)
    print(day)
    print("No available slot found")