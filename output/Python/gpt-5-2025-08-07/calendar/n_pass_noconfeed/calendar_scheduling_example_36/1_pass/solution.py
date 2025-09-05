from typing import List, Tuple

# Helper functions
def time_to_min(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def min_to_time(m: int) -> str:
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

def invert_intervals(busy: List[Tuple[int, int]], bounds: Tuple[int, int]) -> List[Tuple[int, int]]:
    start, end = bounds
    if not busy:
        return [(start, end)]
    busy = merge_intervals([(max(start, s), min(end, e)) for s, e in busy if e > start and s < end])
    free = []
    cur = start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
    return free

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

# Inputs
day = "Monday"
work_start, work_end = time_to_min("09:00"), time_to_min("17:00")
meeting_duration = 60  # minutes

# Busy schedules (Monday)
ryan_busy = [
    (time_to_min("09:00"), time_to_min("09:30")),
    (time_to_min("12:30"), time_to_min("13:00")),
]
ruth_busy = []  # Free all day
denise_busy = [
    (time_to_min("09:30"), time_to_min("10:30")),
    (time_to_min("12:00"), time_to_min("13:00")),
    (time_to_min("14:30"), time_to_min("16:30")),
]

# Preference: Denise does not want to meet after 12:30 (meeting must end by 12:30)
denise_pref_end = time_to_min("12:30")

# Compute free intervals within work hours
bounds = (work_start, work_end)
ryan_free = invert_intervals(ryan_busy, bounds)
ruth_free = invert_intervals(ruth_busy, bounds)
denise_free = invert_intervals(denise_busy, bounds)

# Apply Denise's preference by trimming her free intervals to end no later than 12:30
denise_free_pref = []
for s, e in denise_free:
    if s >= denise_pref_end:
        continue
    denise_free_pref.append((s, min(e, denise_pref_end)))

# Compute common availability
common = [(work_start, work_end)]
for free in (ryan_free, ruth_free, denise_free_pref):
    common = intersect_intervals(common, free)

# Find earliest slot that fits the duration
proposed_start = proposed_end = None
for s, e in common:
    if e - s >= meeting_duration:
        proposed_start = s
        proposed_end = s + meeting_duration
        break

# Output
if proposed_start is None:
    raise RuntimeError("No available slot found, but the problem statement guarantees a solution.")

start_str = min_to_time(proposed_start)
end_str = min_to_time(proposed_end)
print(f"{day} {{{start_str}:{end_str}}}")