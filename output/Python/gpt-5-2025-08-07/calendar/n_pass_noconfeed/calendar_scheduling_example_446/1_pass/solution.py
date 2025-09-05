from typing import List, Tuple

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

def invert_intervals(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
    if not busy:
        return [(ws, we)]
    busy = [(max(ws, s), min(we, e)) for s, e in busy if e > ws and s < we]
    busy = merge_intervals(busy)
    free = []
    cur = ws
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < we:
        free.append((cur, we))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def find_earliest_slot(free_all: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in free_all:
        if e - s >= duration:
            return (s, s + duration)
    return (-1, -1)

# Input data for Monday
day = "Monday"
work_window = (to_minutes("09:00"), to_minutes("17:00"))
duration = 30  # minutes

schedules = {
    "Megan":     [("09:00", "09:30"), ("10:00", "11:00"), ("12:00", "12:30")],
    "Christine": [("09:00", "09:30"), ("11:30", "12:00"), ("13:00", "14:00"), ("15:30", "16:30")],
    "Gabriel":   [],  # free entire day
    "Sara":      [("11:30", "12:00"), ("14:30", "15:00")],
    "Bruce":     [("09:30", "10:00"), ("10:30", "12:00"), ("12:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:30")],
    "Kathryn":   [("10:00", "15:30"), ("16:00", "16:30")],
    "Billy":     [("09:00", "09:30"), ("11:00", "11:30"), ("12:00", "14:00"), ("14:30", "15:30")],
}

# Convert schedules to minutes and compute free intervals per participant
free_by_person = []
for person, busy_list in schedules.items():
    busy_minutes = [(to_minutes(s), to_minutes(e)) for s, e in busy_list]
    free_intervals = invert_intervals(busy_minutes, work_window)
    free_by_person.append(free_intervals)

# Intersect free intervals across all participants
common_free = free_by_person[0]
for free in free_by_person[1:]:
    common_free = intersect_two(common_free, free)

# Find earliest slot that satisfies duration
start, end = find_earliest_slot(common_free, duration)

if start == -1:
    print("No available slot found within constraints.")
else:
    start_str = to_hhmm(start)
    end_str = to_hhmm(end)
    # Output must include both the time range like {HH:MM:HH:MM} and the day of the week
    print(f"{{{start_str}:{end_str}}}")
    print(day)