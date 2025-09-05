from typing import List, Tuple, Dict

# Utilities
def time_to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def clamp_intervals(intervals: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
    clamped = []
    for s, e in intervals:
        s2, e2 = max(s, ws), min(e, we)
        if s2 < e2:
            clamped.append((s2, e2))
    return clamped

def invert_intervals(busy: List[Tuple[int, int]], work_window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = work_window
    busy = merge_intervals(clamp_intervals(busy, work_window))
    if not busy:
        return [(ws, we)]
    free = []
    prev_end = ws
    for s, e in busy:
        if prev_end < s:
            free.append((prev_end, s))
        prev_end = max(prev_end, e)
    if prev_end < we:
        free.append((prev_end, we))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def first_slot_of_duration(intervals: List[Tuple[int, int]], duration: int) -> Tuple[int, int] | None:
    for s, e in intervals:
        if e - s >= duration:
            return (s, s + duration)
    return None

# Problem setup
work_hours = (time_to_minutes("09:00"), time_to_minutes("17:00"))
duration = 30  # minutes

participants_busy: Dict[str, Dict[str, List[Tuple[int, int]]]] = {
    "Ryan": {
        "Monday": [(time_to_minutes("09:30"), time_to_minutes("10:00")),
                   (time_to_minutes("11:00"), time_to_minutes("12:00")),
                   (time_to_minutes("13:00"), time_to_minutes("13:30")),
                   (time_to_minutes("15:30"), time_to_minutes("16:00"))],
        "Tuesday": [(time_to_minutes("11:30"), time_to_minutes("12:30")),
                    (time_to_minutes("15:30"), time_to_minutes("16:00"))],
        "Wednesday": [(time_to_minutes("12:00"), time_to_minutes("13:00")),
                      (time_to_minutes("15:30"), time_to_minutes("16:00")),
                      (time_to_minutes("16:30"), time_to_minutes("17:00"))],
    },
    "Adam": {
        "Monday": [(time_to_minutes("09:00"), time_to_minutes("10:30")),
                   (time_to_minutes("11:00"), time_to_minutes("13:30")),
                   (time_to_minutes("14:00"), time_to_minutes("16:00")),
                   (time_to_minutes("16:30"), time_to_minutes("17:00"))],
        "Tuesday": [(time_to_minutes("09:00"), time_to_minutes("10:00")),
                    (time_to_minutes("10:30"), time_to_minutes("15:30")),
                    (time_to_minutes("16:00"), time_to_minutes("17:00"))],
        "Wednesday": [(time_to_minutes("09:00"), time_to_minutes("09:30")),
                      (time_to_minutes("10:00"), time_to_minutes("11:00")),
                      (time_to_minutes("11:30"), time_to_minutes("14:30")),
                      (time_to_minutes("15:00"), time_to_minutes("15:30")),
                      (time_to_minutes("16:00"), time_to_minutes("16:30"))],
    }
}

# Constraints:
# - Meeting days allowed: Monday, Tuesday, Wednesday
# - Ryan cannot meet on Wednesday => exclude Wednesday
# - Adam would like to avoid Monday before 14:30 => prefer Tuesday first, then Monday 14:30-17:00, then Monday 09:00-14:30
preferences = [
    ("Tuesday", ("09:00", "17:00")),      # Highest preference: Tuesday anytime within work hours
    ("Monday",  ("14:30", "17:00")),      # Next: Monday but after 14:30
    ("Monday",  ("09:00", "14:30")),      # Least preferred Monday window (if needed)
    # Wednesday excluded due to Ryan's constraint
]

# Precompute free intervals for each participant/day
participants_free: Dict[str, Dict[str, List[Tuple[int, int]]]] = {}
for person, days in participants_busy.items():
    participants_free[person] = {}
    for day, busy in days.items():
        # Only consider within work hours
        free = invert_intervals(busy, work_hours)
        participants_free[person][day] = free

# Search according to preferences
proposal = None
for day, window_str in preferences:
    ws, we = map(time_to_minutes, window_str)
    window = (ws, we)

    # Skip days not available for someone (e.g., Ryan can't on Wednesday)
    if day == "Wednesday":
        continue

    # Gather free intervals for both participants on this day, clamped to preference window
    try:
        r_free = clamp_intervals(participants_free["Ryan"][day], window)
        a_free = clamp_intervals(participants_free["Adam"][day], window)
    except KeyError:
        continue  # if any participant doesn't have data for the day

    # Intersect their availabilities
    common = intersect_two(r_free, a_free)

    # Find the first 30-minute slot
    slot = first_slot_of_duration(common, duration)
    if slot:
        start, end = slot
        proposal = (day, minutes_to_time(start), minutes_to_time(end))
        break

# Output
if proposal:
    day, start_str, end_str = proposal
    print(day)
    print(f"{{{start_str}:{end_str}}}")
else:
    print("No suitable slot found.")