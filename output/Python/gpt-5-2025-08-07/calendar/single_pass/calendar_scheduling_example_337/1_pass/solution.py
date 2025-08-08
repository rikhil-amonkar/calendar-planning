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
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def invert_to_free(busy: List[Tuple[int, int]], day_start: int, day_end: int) -> List[Tuple[int, int]]:
    busy = [(max(day_start, s), min(day_end, e)) for s, e in busy if e > day_start and s < day_end]
    busy = merge_intervals(busy)
    free = []
    prev = day_start
    for s, e in busy:
        if prev < s:
            free.append((prev, s))
        prev = max(prev, e)
    if prev < day_end:
        free.append((prev, day_end))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def find_meeting_slot(schedules: dict, work_start: str, work_end: str, duration_min: int) -> Tuple[str, str, str]:
    day = "Monday"
    day_start = to_minutes(work_start)
    day_end = to_minutes(work_end)

    # Convert busy schedules to minutes and compute free intervals for each participant
    all_free = None
    for person, meetings in schedules.items():
        busy_min = [(to_minutes(s), to_minutes(e)) for s, e in meetings]
        free = invert_to_free(busy_min, day_start, day_end)
        if all_free is None:
            all_free = free
        else:
            all_free = intersect_intervals(all_free, free)

    # Find the earliest slot that fits the duration
    for s, e in all_free or []:
        if e - s >= duration_min:
            start_str = to_hhmm(s)
            end_str = to_hhmm(s + duration_min)
            return day, start_str, end_str

    raise ValueError("No available slot found")

if __name__ == "__main__":
    # Given task data
    schedules = {
        "John": [("11:30", "12:00"), ("14:00", "14:30")],
        "Megan": [("12:00", "12:30"), ("14:00", "15:00"), ("15:30", "16:00")],
        "Brandon": [],
        "Kimberly": [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "14:30"), ("15:00", "16:00"), ("16:30", "17:00")],
        "Sean": [("10:00", "11:00"), ("11:30", "14:00"), ("15:00", "15:30")],
        "Lori": [("09:00", "09:30"), ("10:30", "12:00"), ("13:00", "14:30"), ("16:00", "16:30")],
    }

    work_start = "09:00"
    work_end = "17:00"
    duration_min = 30

    day, start, end = find_meeting_slot(schedules, work_start, work_end, duration_min)
    print(day)
    print(f"{{{start}:{end}}}")