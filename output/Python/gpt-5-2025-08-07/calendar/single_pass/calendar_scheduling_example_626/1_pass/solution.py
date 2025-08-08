from typing import List, Tuple, Dict

# Helpers to convert between "HH:MM" and minutes since midnight
def time_to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m: int) -> str:
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

Interval = Tuple[int, int]

def merge_intervals(intervals: List[Interval]) -> List[Interval]:
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

def invert_within(busy: List[Interval], window: Interval) -> List[Interval]:
    ws, we = window
    if ws >= we:
        return []
    if not busy:
        return [(ws, we)]
    busy = merge_intervals([(max(ws, s), min(we, e)) for s, e in busy if e > ws and s < we])

    free = []
    cur = ws
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < we:
        free.append((cur, we))
    return free

def intersect_two(a: List[Interval], b: List[Interval]) -> List[Interval]:
    i = j = 0
    result = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            result.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return result

def find_first_slot(days: List[str],
                    participants_busy: Dict[str, Dict[str, List[Tuple[str, str]]]],
                    work_window: Tuple[str, str],
                    duration_minutes: int) -> Tuple[str, Interval]:
    ws, we = map(time_to_minutes, work_window)
    for day in days:
        # Compute free intervals for each participant on this day
        participants_free = []
        for person, cal in participants_busy.items():
            busy_str = cal.get(day, [])
            busy = [(time_to_minutes(s), time_to_minutes(e)) for s, e in busy_str]
            free = invert_within(busy, (ws, we))
            participants_free.append(free)

        # Intersect free intervals across all participants
        common = participants_free[0]
        for pf in participants_free[1:]:
            common = intersect_two(common, pf)
            if not common:
                break

        # Find first interval of sufficient length
        for s, e in common:
            if e - s >= duration_minutes:
                return day, (s, s + duration_minutes)
    raise ValueError("No suitable slot found")

# Define the scenario
days_considered = ["Monday", "Tuesday"]
work_hours = ("09:00", "17:00")
duration = 60  # minutes

participants = {
    "Patricia": {
        "Monday": [("10:00", "10:30"), ("11:30", "12:00"), ("13:00", "13:30"), ("14:30", "15:30"), ("16:00", "16:30")],
        "Tuesday": [("10:00", "10:30"), ("11:00", "12:00"), ("14:00", "16:00"), ("16:30", "17:00")],
    },
    "Jesse": {
        "Monday": [("09:00", "17:00")],
        "Tuesday": [("11:00", "11:30"), ("12:00", "12:30"), ("13:00", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")],
    }
}

day, (start, end) = find_first_slot(days_considered, participants, work_hours, duration)
start_str, end_str = minutes_to_time(start), minutes_to_time(end)

# Output: day of week and time range in {HH:MM:HH:MM}
print(day)
print(f"{{{start_str}:{end_str}}}")