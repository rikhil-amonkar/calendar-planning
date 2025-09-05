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

def invert_intervals(busy: List[Tuple[int, int]], day_start: int, day_end: int) -> List[Tuple[int, int]]:
    busy = merge_intervals(busy)
    free = []
    cur = day_start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < day_end:
        free.append((cur, day_end))
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

def intersect_all(lists: List[List[Tuple[int, int]]]) -> List[Tuple[int, int]]:
    if not lists:
        return []
    inter = lists[0]
    for lst in lists[1:]:
        inter = intersect_two(inter, lst)
        if not inter:
            break
    return inter

def find_slot(common_free: List[Tuple[int, int]], duration: int, prefer_end_before: int = None) -> Tuple[int, int]:
    # First pass: honor preference if provided (slot must end <= prefer_end_before)
    if prefer_end_before is not None:
        for s, e in common_free:
            latest_end = min(e, prefer_end_before)
            if s + duration <= latest_end:
                return s, s + duration
    # Second pass: any earliest slot
    for s, e in common_free:
        if s + duration <= e:
            return s, s + duration
    return None

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    schedules = {
        "Raymond": [("09:00","09:30"), ("11:30","12:00"), ("13:00","13:30"), ("15:00","15:30")],
        "Billy":   [("10:00","10:30"), ("12:00","13:00"), ("16:30","17:00")],
        "Donald":  [("09:00","09:30"), ("10:00","11:00"), ("12:00","13:00"), ("14:00","14:30"), ("16:00","17:00")],
    }

    # Convert busy schedules to minutes
    busy_minutes = {
        person: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
        for person, intervals in schedules.items()
    }

    # Compute free intervals within working hours for each participant
    free_by_person = [
        invert_intervals(busy_minutes[person], work_start, work_end)
        for person in schedules.keys()
    ]

    # Intersect all free intervals
    common_free = intersect_all(free_by_person)

    # Preference: Billy would like to avoid more meetings on Monday after 15:00
    prefer_end_before = to_minutes("15:00")

    slot = find_slot(common_free, duration, prefer_end_before=prefer_end_before)
    if slot is None:
        raise RuntimeError("No available slot found, but one was expected to exist.")
    start, end = slot

    # Output in required format: {HH:MM:HH:MM} and the day of the week
    print(f"{{{to_hhmm(start)}:{to_hhmm(end)}}} {day}")

if __name__ == "__main__":
    main()