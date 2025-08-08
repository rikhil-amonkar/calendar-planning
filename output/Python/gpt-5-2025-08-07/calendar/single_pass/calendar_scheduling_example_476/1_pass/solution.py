from typing import List, Tuple

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

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

def clip_to_bounds(intervals: List[Tuple[int, int]], bounds: Tuple[int, int]) -> List[Tuple[int, int]]:
    b_start, b_end = bounds
    clipped = []
    for s, e in intervals:
        s = max(s, b_start)
        e = min(e, b_end)
        if s < e:
            clipped.append((s, e))
    return merge_intervals(clipped)

def invert_within_bounds(busy: List[Tuple[int, int]], bounds: Tuple[int, int]) -> List[Tuple[int, int]]:
    b_start, b_end = bounds
    busy = merge_intervals(clip_to_bounds(busy, bounds))
    free = []
    cur = b_start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < b_end:
        free.append((cur, b_end))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i, j = 0, 0
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

# Data setup
day = "Monday"
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
work_bounds = (work_start, work_end)
meeting_duration = 30  # minutes

schedules = {
    "Daniel": [],  # no meetings
    "Kathleen": [("14:30", "15:30")],
    "Carolyn": [("12:00", "12:30"), ("13:00", "13:30")],
    "Roger": [],  # preference handled below
    "Cheryl": [("09:00", "09:30"), ("10:00", "11:30"), ("12:30", "13:30"), ("14:00", "17:00")],
    "Virginia": [("09:30", "11:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "15:30"), ("16:00", "17:00")],
    "Angela": [("09:30", "10:00"), ("10:30", "11:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:00", "16:30")],
}

# Convert schedules to minutes
busy_minutes = {}
for person, intervals in schedules.items():
    busy_minutes[person] = [(to_minutes(s), to_minutes(e)) for s, e in intervals]

# Apply Roger's preference: rather not meet before 12:30 (treat as a hard constraint)
busy_minutes["Roger"].append((work_start, to_minutes("12:30")))

# Compute free intervals for each participant
free_by_person = {}
for person, busy in busy_minutes.items():
    free_by_person[person] = invert_within_bounds(busy, work_bounds)

# Intersect free intervals across all participants
participants = list(free_by_person.keys())
common_free = free_by_person[participants[0]][:]
for person in participants[1:]:
    common_free = intersect_intervals(common_free, free_by_person[person])
    if not common_free:
        break

# Find the earliest slot of required duration
proposed = None
for s, e in common_free:
    if e - s >= meeting_duration:
        proposed = (s, s + meeting_duration)
        break

if not proposed:
    raise RuntimeError("No suitable meeting time found, though a solution is expected to exist.")

start_str, end_str = to_hhmm(proposed[0]), to_hhmm(proposed[1])

# Output: time range and day
print(f"{{{start_str}:{end_str}}}")
print(day)