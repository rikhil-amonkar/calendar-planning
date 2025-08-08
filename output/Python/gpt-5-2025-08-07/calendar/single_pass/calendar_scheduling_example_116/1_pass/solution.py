# Meeting Scheduler for Adam, John, Stephanie, and Anna on Monday

from typing import List, Tuple

def parse_time(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def format_time(m: int) -> str:
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

def invert_within(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
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

def main():
    day = "Monday"
    work_start, work_end = parse_time("09:00"), parse_time("17:00")
    duration = 30  # minutes

    schedules = {
        "Adam":       [("14:00", "15:00")],
        "John":       [("13:00", "13:30"), ("14:00", "14:30"), ("15:30", "16:00"), ("16:30", "17:00")],
        "Stephanie":  [("09:30", "10:00"), ("10:30", "11:00"), ("11:30", "16:00"), ("16:30", "17:00")],
        "Anna":       [("09:30", "10:00"), ("12:00", "12:30"), ("13:00", "15:30"), ("16:30", "17:00")],
    }

    # Convert schedules to minutes
    busy_minutes = {
        person: [(parse_time(s), parse_time(e)) for s, e in intervals]
        for person, intervals in schedules.items()
    }

    # Compute free intervals within work hours
    work_window = (work_start, work_end)
    free_by_person = {
        person: invert_within(busy, work_window)
        for person, busy in busy_minutes.items()
    }

    # Intersect all free intervals
    all_free = [(work_start, work_end)]
    for person in ["Adam", "John", "Stephanie", "Anna"]:
        all_free = intersect_intervals(all_free, free_by_person[person])

    # Preference: Anna would rather not meet before 14:30
    earliest_preferred_start = parse_time("14:30")

    # Find earliest feasible slot respecting preference
    for s, e in all_free:
        start = max(s, earliest_preferred_start)
        if start + duration <= e:
            end = start + duration
            time_range = f"{format_time(start)}:{format_time(end)}"
            print(f"{{{time_range}}}")
            print(day)
            return

    # Fallback (should not occur per problem statement)
    print("{No available time}")
    print(day)

if __name__ == "__main__":
    main()