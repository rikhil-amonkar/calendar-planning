from typing import List, Tuple

# Utilities
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time_str(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def clip_intervals(intervals: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    clipped = []
    for s, e in intervals:
        s2, e2 = max(s, start), min(e, end)
        if s2 < e2:
            clipped.append((s2, e2))
    return merge_intervals(clipped)

def invert_to_free(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    busy = merge_intervals(clip_intervals(busy, start, end))
    free = []
    cursor = start
    for s, e in busy:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < end:
        free.append((cursor, end))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    res = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            res.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return res

# Setup
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes

participants_busy = {
    "Ronald": [],
    "Stephen": [("10:00", "10:30"), ("12:00", "12:30")],
    "Brittany": [("11:00", "11:30"), ("13:30", "14:00"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Dorothy": [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "12:30"), ("13:00", "15:00"), ("15:30", "17:00")],
    "Rebecca": [("09:30", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:00", "17:00")],
    "Jordan": [("09:00", "09:30"), ("10:00", "11:00"), ("11:30", "12:00"), ("13:00", "15:00"), ("15:30", "16:30")],
}

# Convert busy strings to minutes and compute free intervals for each participant
free_schedules = []
for name, intervals in participants_busy.items():
    busy_in_minutes = [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    free_intervals = invert_to_free(busy_in_minutes, work_start, work_end)
    free_schedules.append(free_intervals)

# Intersect all free schedules
common_free = free_schedules[0]
for fs in free_schedules[1:]:
    common_free = intersect_intervals(common_free, fs)

# Find the earliest slot that fits the duration
proposed_start = proposed_end = None
for s, e in common_free:
    if e - s >= duration:
        proposed_start = s
        proposed_end = s + duration
        break

# Output
if proposed_start is not None:
    start_str = to_time_str(proposed_start)
    end_str = to_time_str(proposed_end)
    print(f"{day} {{{start_str}:{end_str}}}")
else:
    # Fallback (shouldn't happen per problem statement that a solution exists)
    print(f"{day} {{No available slot}}")