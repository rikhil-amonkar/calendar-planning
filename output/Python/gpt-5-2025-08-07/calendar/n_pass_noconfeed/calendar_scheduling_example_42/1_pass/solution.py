from typing import List, Tuple

def to_minutes(time_str: str) -> int:
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

def to_hhmm(minutes: int) -> str:
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def normalize_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    # Merge overlapping intervals and sort
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

def get_free_intervals(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    busy = normalize_intervals([(max(work_start, s), min(work_end, e)) for s, e in busy if e > work_start and s < work_end])
    free = []
    current = work_start
    for s, e in busy:
        if s > current:
            free.append((current, s))
        current = max(current, e)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def find_meeting_slot(schedules: dict, work_hours: Tuple[str, str], duration_minutes: int, day: str) -> Tuple[str, str]:
    work_start = to_minutes(work_hours[0])
    work_end = to_minutes(work_hours[1])

    # Compute free intervals for each participant
    all_free = []
    for person, busy_strs in schedules.items():
        busy = [(to_minutes(s), to_minutes(e)) for s, e in busy_strs]
        free = get_free_intervals(busy, work_start, work_end)
        all_free.append(free)

    # Intersect all free intervals
    common = all_free[0]
    for free in all_free[1:]:
        common = intersect_intervals(common, free)

    # Find the earliest interval that fits the duration
    for s, e in common:
        if e - s >= duration_minutes:
            start_str = to_hhmm(s)
            end_str = to_hhmm(s + duration_minutes)
            return day, f"{start_str}:{end_str}"

    raise ValueError("No common slot found")

if __name__ == "__main__":
    # Problem data
    day = "Monday"
    work_hours = ("09:00", "17:00")
    duration_minutes = 60
    schedules = {
        "Julie": [("09:00", "09:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:30", "14:00"), ("16:00", "17:00")],
        "Sean":  [("09:00", "09:30"), ("13:00", "13:30"), ("15:00", "15:30"), ("16:00", "16:30")],
        "Lori":  [("10:00", "10:30"), ("11:00", "13:00"), ("15:30", "17:00")],
    }

    day_out, time_range = find_meeting_slot(schedules, work_hours, duration_minutes, day)
    print(f"{day_out} {{{time_range}}}")