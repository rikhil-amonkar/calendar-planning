from typing import List, Tuple

# Time helpers
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
    for start, end in intervals[1:]:
        last_start, last_end = merged[-1]
        if start <= last_end:
            merged[-1] = (last_start, max(last_end, end))
        else:
            merged.append((start, end))
    return merged

def clamp_intervals_to_window(intervals: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
    clamped = []
    for s, e in intervals:
        s2, e2 = max(s, ws), min(e, we)
        if s2 < e2:
            clamped.append((s2, e2))
    return clamped

def invert_busy_to_free(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
    if not busy:
        return [(ws, we)]
    busy = merge_intervals(clamp_intervals_to_window(busy, window))
    free = []
    cursor = ws
    for s, e in busy:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < we:
        free.append((cursor, we))
    return free

def find_earliest_slot(free: List[Tuple[int, int]], duration: int) -> Tuple[int, int] | None:
    for s, e in free:
        if e - s >= duration:
            return (s, s + duration)
    return None

# Problem setup
work_window = (to_minutes("09:00"), to_minutes("17:00"))
meeting_duration = 60  # minutes
days = ["Monday", "Tuesday", "Wednesday"]

# Participants' busy schedules
# Patrick: free all week (no busy intervals)
patrick_busy = {
    "Monday": [],
    "Tuesday": [],
    "Wednesday": [],
}

roy_busy = {
    "Monday": [("10:00", "11:30"), ("12:00", "13:00"), ("14:00", "14:30"), ("15:00", "17:00")],
    "Tuesday": [("10:30", "11:30"), ("12:00", "14:30"), ("15:00", "15:30"), ("16:00", "17:00")],
    "Wednesday": [("09:30", "11:30"), ("12:30", "14:00"), ("14:30", "15:30"), ("16:30", "17:00")],
}

# Convert to minutes
def convert_day_busy(busy_dict):
    converted = {}
    for day, intervals in busy_dict.items():
        converted[day] = [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    return converted

patrick_busy_m = convert_day_busy(patrick_busy)
roy_busy_m = convert_day_busy(roy_busy)

participants = [patrick_busy_m, roy_busy_m]

# Search earliest feasible slot
for day in days:
    # Gather all busy intervals for this day across participants
    all_busy = []
    for p in participants:
        all_busy.extend(p.get(day, []))
    all_busy = merge_intervals(all_busy)
    # Compute free intervals within work window
    free = invert_busy_to_free(all_busy, work_window)
    slot = find_earliest_slot(free, meeting_duration)
    if slot:
        start, end = slot
        print(day)
        print(f"{{{to_hhmm(start)}:{to_hhmm(end)}}}")
        break