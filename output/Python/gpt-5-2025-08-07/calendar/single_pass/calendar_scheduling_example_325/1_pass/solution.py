# Meeting scheduler for Monday between 09:00 and 17:00 with 30-minute duration

from typing import List, Tuple

TimeInterval = Tuple[int, int]

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals: List[TimeInterval]) -> List[TimeInterval]:
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def complement_intervals(busy: List[TimeInterval], window: TimeInterval) -> List[TimeInterval]:
    ws, we = window
    busy = merge_intervals([(max(ws, s), min(we, e)) for s, e in busy if e > ws and s < we])
    free: List[TimeInterval] = []
    cur = ws
    for s, e in busy:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < we:
        free.append((cur, we))
    return free

def intersect_two(a: List[TimeInterval], b: List[TimeInterval]) -> List[TimeInterval]:
    i = j = 0
    res: List[TimeInterval] = []
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

def find_meeting_slot(all_free: List[List[TimeInterval]], duration: int) -> TimeInterval:
    # Intersect all participants' free intervals
    common = all_free[0]
    for person_free in all_free[1:]:
        common = intersect_two(common, person_free)
        if not common:
            return (-1, -1)
    # Pick earliest slot with required duration
    for s, e in common:
        if e - s >= duration:
            return (s, s + duration)
    return (-1, -1)

def main():
    day = "Monday"
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    duration = 30  # minutes

    schedules = {
        "Jose":  [("11:00","11:30"), ("12:30","13:00")],
        "Keith": [("14:00","14:30"), ("15:00","15:30")],
        "Logan": [("09:00","10:00"), ("12:00","12:30"), ("15:00","15:30")],
        "Megan": [("09:00","10:30"), ("11:00","12:00"), ("13:00","13:30"), ("14:30","16:30")],
        "Gary":  [("09:00","09:30"), ("10:00","10:30"), ("11:30","13:00"), ("13:30","14:00"), ("14:30","16:30")],
        "Bobby": [("11:00","11:30"), ("12:00","12:30"), ("13:00","16:00")],
    }

    # Convert busy schedules to minutes
    busy_minutes = {
        person: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
        for person, intervals in schedules.items()
    }

    work_window = (work_start, work_end)

    # Compute free intervals for each person
    free_by_person: List[List[TimeInterval]] = []
    for person, busy in busy_minutes.items():
        free = complement_intervals(busy, work_window)

        # Apply Jose's preference: do not meet after 15:30 (cap availability to end at 15:30)
        if person == "Jose":
            cap = (work_start, to_minutes("15:30"))
            free = intersect_two(free, [cap])

        free_by_person.append(free)

    start, end = find_meeting_slot(free_by_person, duration)

    # Output
    if start >= 0:
        start_str, end_str = to_hhmm(start), to_hhmm(end)
        print(day)
        print(f"{{{start_str}:{end_str}}}")
    else:
        print(day)
        print("{No available slot}")

if __name__ == "__main__":
    main()