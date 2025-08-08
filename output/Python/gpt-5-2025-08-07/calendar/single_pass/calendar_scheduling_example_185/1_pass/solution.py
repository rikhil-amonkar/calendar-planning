from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.strip().split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

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

def invert_within_workday(busy: List[Tuple[int, int]], day_start: int, day_end: int) -> List[Tuple[int, int]]:
    busy = [(max(day_start, s), min(day_end, e)) for s, e in busy if e > day_start and s < day_end]
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

def choose_slot(avails: List[Tuple[int, int]], duration: int, preferred_start: int = None) -> Tuple[int, int]:
    # Try respecting preference first
    if preferred_start is not None:
        for s, e in avails:
            start = max(s, preferred_start)
            if start + duration <= e:
                return start, start + duration
    # Fallback to earliest available
    for s, e in avails:
        if s + duration <= e:
            return s, s + duration
    return None

def main():
    day = "Monday"
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    duration = 30  # minutes

    schedules = {
        "Kimberly": [("10:00","10:30"), ("11:00","12:00"), ("16:00","16:30")],
        "Megan":    [],  # prefers after 10:00
        "Marie":    [("10:00","11:00"), ("11:30","15:00"), ("16:00","16:30")],
        "Diana":    [("9:30","10:00"), ("10:30","14:30"), ("15:30","17:00")],
    }

    # Convert to minutes
    busy_minutes = {
        person: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
        for person, intervals in schedules.items()
    }

    # Compute free intervals per person
    free_by_person = {
        person: invert_within_workday(busy, work_start, work_end)
        for person, busy in busy_minutes.items()
    }

    # Intersect all free intervals
    people = list(free_by_person.keys())
    common_free = free_by_person[people[0]]
    for p in people[1:]:
        common_free = intersect_intervals(common_free, free_by_person[p])

    # Preference: Megan would like to avoid meetings before 10:00 on Monday
    preferred_start = to_minutes("10:00")

    slot = choose_slot(common_free, duration, preferred_start=preferred_start)
    if not slot:
        raise RuntimeError("No suitable meeting time found, but a solution was expected.")

    start_str, end_str = to_hhmm(slot[0]), to_hhmm(slot[1])

    # Output: day and time range in HH:MM:HH:MM, with braces as example indicates
    print(day)
    print(f"{{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()