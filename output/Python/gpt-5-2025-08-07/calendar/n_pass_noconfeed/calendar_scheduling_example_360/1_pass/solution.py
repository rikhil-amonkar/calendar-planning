from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:  # overlap or touch
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def complement_intervals(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    free = []
    start, end = window
    current = start
    for s, e in busy:
        if s > current:
            free.append((current, s))
        current = max(current, e)
    if current < end:
        free.append((current, end))
    return free

def find_slot(free: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in free:
        if e - s >= duration:
            return (s, s + duration)
    return None

day = "Monday"
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
meeting_duration = 30  # minutes

schedules = {
    "Emily": [("10:00", "10:30"), ("16:00", "16:30")],
    "Mason": [],
    "Maria": [("10:30", "11:00"), ("14:00", "14:30")],
    "Carl": [("09:30", "10:00"), ("10:30", "12:30"), ("13:30", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")],
    "David": [("09:30", "11:00"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:00", "15:00"), ("16:00", "17:00")],
    "Frank": [("09:30", "10:30"), ("11:00", "11:30"), ("12:30", "13:30"), ("14:30", "17:00")],
}

# Collect all busy intervals within work window
busy_all = []
for intervals in schedules.values():
    for s, e in intervals:
        ms, me = to_minutes(s), to_minutes(e)
        # Clamp to work window
        ms = max(ms, work_start)
        me = min(me, work_end)
        if ms < me:
            busy_all.append((ms, me))

# Merge busy intervals to get the union (times when anyone is busy)
busy_merged = merge_intervals(busy_all)

# Get global free intervals (times when everyone is free)
free_global = complement_intervals(busy_merged, (work_start, work_end))

# Find earliest slot with required duration
slot = find_slot(free_global, meeting_duration)

if slot:
    start_str, end_str = to_hhmm(slot[0]), to_hhmm(slot[1])
    print(day)
    print(f"{start_str}:{end_str}")
else:
    # Fallback (should not happen per problem statement)
    print(day)
    print("No available slot")