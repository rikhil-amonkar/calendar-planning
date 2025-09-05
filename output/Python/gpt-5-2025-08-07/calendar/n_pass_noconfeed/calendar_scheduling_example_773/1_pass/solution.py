from typing import List, Tuple, Dict

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_timestr(m: int) -> str:
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

def invert_intervals(busy: List[Tuple[int, int]], day_start: int, day_end: int) -> List[Tuple[int, int]]:
    if not busy:
        return [(day_start, day_end)]
    free = []
    cur = day_start
    for s, e in busy:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < day_end:
        free.append((cur, day_end))
    return free

def find_earliest_slot(busy_map: Dict[str, List[Tuple[str, str]]],
                       work_start: str, work_end: str,
                       duration_min: int,
                       day_order: List[str]) -> Tuple[str, Tuple[int, int]]:
    ws, we = to_minutes(work_start), to_minutes(work_end)
    for day in day_order:
        # Combine all participants' busy intervals for this day
        busy_minutes: List[Tuple[int, int]] = []
        for intervals in busy_map.get(day, []):
            for s, e in intervals:
                busy_minutes.append((to_minutes(s), to_minutes(e)))
        busy_merged = merge_intervals(busy_minutes)
        free = invert_intervals(busy_merged, ws, we)
        for fs, fe in free:
            if fe - fs >= duration_min:
                return day, (fs, fs + duration_min)
    raise ValueError("No available slot found")

# Define participants' calendars
days = ["Monday", "Tuesday", "Wednesday"]
work_start = "09:00"
work_end = "17:00"
duration_min = 60

# Patrick is free (no busy intervals)
patrick_busy = {day: [] for day in days}

# Roy's busy schedule
roy_busy_raw = {
    "Monday": [("10:00","11:30"), ("12:00","13:00"), ("14:00","14:30"), ("15:00","17:00")],
    "Tuesday": [("10:30","11:30"), ("12:00","14:30"), ("15:00","15:30"), ("16:00","17:00")],
    "Wednesday": [("09:30","11:30"), ("12:30","14:00"), ("14:30","15:30"), ("16:30","17:00")],
}

# Build a combined busy map: per day, list of each participant's intervals
busy_map: Dict[str, List[List[Tuple[str, str]]]] = {day: [] for day in days}
for day in days:
    # Patrick
    busy_map[day].append(patrick_busy.get(day, []))
    # Roy
    busy_map[day].append(roy_busy_raw.get(day, []))

day, (start_min, end_min) = find_earliest_slot(busy_map, work_start, work_end, duration_min, days)
time_range = f"{to_timestr(start_min)}:{to_timestr(end_min)}"
print(f"{day} {{{time_range}}}")