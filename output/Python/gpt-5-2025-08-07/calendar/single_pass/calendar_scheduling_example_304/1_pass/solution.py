# Meeting scheduler for the given participants and constraints

from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def complement_within(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    start, end = window
    free = []
    cur = start
    for b_start, b_end in sorted(busy):
        if b_end <= cur:
            continue
        if b_start > end:
            break
        if b_start > cur:
            free.append((cur, min(b_start, end)))
        cur = max(cur, b_end)
        if cur >= end:
            break
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

# Data
day = "Monday"
work_window = (to_minutes("09:00"), to_minutes("17:00"))
meeting_minutes = 30

schedules = {
    "Christine": [("09:30", "10:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("16:00", "16:30")],
    "Janice":    [],  # wide open
    "Bobby":     [("12:00", "12:30"), ("14:30", "15:00")],
    "Elizabeth": [("09:00", "09:30"), ("11:30", "13:00"), ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "17:00")],
    "Tyler":     [("09:00", "11:00"), ("12:00", "12:30"), ("13:00", "13:30"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Edward":    [("09:00", "09:30"), ("10:00", "11:00"), ("11:30", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")],
}

# Convert busy times to minutes
busy_minutes = {
    name: [(to_minutes(s), to_minutes(e)) for s, e in times]
    for name, times in schedules.items()
}

# Compute free intervals for each participant within work window
free_by_person = {
    name: complement_within(times, work_window)
    for name, times in busy_minutes.items()
}

# Intersect all free intervals
participants = list(free_by_person.keys())
common_free = free_by_person[participants[0]][:]
for name in participants[1:]:
    common_free = intersect_intervals(common_free, free_by_person[name])

# Filter intervals that can fit the meeting
candidates = [(s, e) for s, e in common_free if e - s >= meeting_minutes]

# Apply Janice's preference: rather not meet after 13:00
prefer_before = to_minutes("13:00")
preferred = [(s, e) for s, e in candidates if s + meeting_minutes <= prefer_before]

# Choose the earliest feasible start
def pick_slot(slots: List[Tuple[int, int]]) -> Tuple[int, int]:
    # pick earliest start; slot length is meeting_minutes, so we return (start, start+meeting_minutes)
    earliest = min(slots, key=lambda x: x[0])
    return earliest[0], earliest[0] + meeting_minutes

if preferred:
    start, end = pick_slot(preferred)
else:
    start, end = pick_slot(candidates)

# Output
print(day)
print(f"{{{to_hhmm(start)}:{to_hhmm(end)}}}")