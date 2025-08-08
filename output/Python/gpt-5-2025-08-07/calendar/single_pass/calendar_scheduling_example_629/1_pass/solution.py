from typing import List, Tuple, Dict

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

def complement_intervals(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    start, end = window
    if start >= end:
        return []
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

def intersect_many(lists: List[List[Tuple[int, int]]]) -> List[Tuple[int, int]]:
    if not lists:
        return []
    res = lists[0]
    for lst in lists[1:]:
        res = intersect_two(res, lst)
        if not res:
            break
    return res

def first_slot_of_duration(intervals: List[Tuple[int, int]], duration: int) -> Tuple[int, int] | None:
    for s, e in intervals:
        if e - s >= duration:
            return (s, s + duration)
    return None

# Data
work_window = (to_minutes("09:00"), to_minutes("17:00"))
duration = 30  # minutes
days = ["Monday", "Tuesday"]

schedules: Dict[str, Dict[str, List[Tuple[int, int]]]] = {
    "Margaret": {
        "Monday": [(to_minutes("10:30"), to_minutes("11:00")),
                   (to_minutes("11:30"), to_minutes("12:00")),
                   (to_minutes("13:00"), to_minutes("13:30")),
                   (to_minutes("15:00"), to_minutes("17:00"))],
        "Tuesday": [(to_minutes("12:00"), to_minutes("12:30"))],
    },
    "Alexis": {
        "Monday": [(to_minutes("09:30"), to_minutes("11:30")),
                   (to_minutes("12:30"), to_minutes("13:00")),
                   (to_minutes("14:00"), to_minutes("17:00"))],
        "Tuesday": [(to_minutes("09:00"), to_minutes("09:30")),
                    (to_minutes("10:00"), to_minutes("10:30")),
                    (to_minutes("14:00"), to_minutes("16:30"))],
    }
}

# Constraints:
# - Meeting only on Monday or Tuesday (already our domain)
# - Margaret does not want to meet on Monday -> restrict to Tuesday
# - Tuesday before 14:30 -> ensure meeting ends by 14:30
allowed_days = ["Tuesday"]
tuesday_end_cap = to_minutes("14:30")

# Compute candidate
selected_day = None
selected_slot = None

for day in allowed_days:
    # Day-specific allowed window
    day_window = work_window
    if day == "Tuesday":
        # Meeting must end by 14:30
        day_window = (work_window[0], min(work_window[1], tuesday_end_cap))

    # Build free intervals per participant
    free_by_participant = []
    for person, per_day in schedules.items():
        busy = per_day.get(day, [])
        free = complement_intervals(busy, day_window)
        free_by_participant.append(free)

    # Intersect across all participants
    common_free = intersect_many(free_by_participant)

    # Find earliest slot of required duration
    slot = first_slot_of_duration(common_free, duration)
    if slot:
        selected_day = day
        selected_slot = slot
        break

if not selected_slot:
    raise RuntimeError("No suitable time found, but problem statement guarantees a solution.")

start_str = to_hhmm(selected_slot[0])
end_str = to_hhmm(selected_slot[1])

# Output: include both day and time in HH:MM:HH:MM
print(selected_day)
print(f"{start_str}:{end_str}")