from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:  # overlaps or touches
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def invert_to_free(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    if not busy:
        return [(work_start, work_end)]
    free = []
    prev = work_start
    for s, e in busy:
        s = max(s, work_start)
        e = min(e, work_end)
        if s > prev:
            free.append((prev, s))
        prev = max(prev, e)
    if prev < work_end:
        free.append((prev, work_end))
    return free

def intersect(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def find_meeting_slot(all_free: List[List[Tuple[int, int]]], duration: int) -> Tuple[int, int]:
    # Intersect all participants' free intervals
    common = all_free[0]
    for free in all_free[1:]:
        common = intersect(common, free)
        if not common:
            return (-1, -1)
    # Find the first interval with enough duration
    for s, e in common:
        if e - s >= duration:
            return (s, s + duration)
    return (-1, -1)

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    schedules = {
        "Joan":     [("11:30","12:00"), ("14:30","15:00")],
        "Megan":    [("09:00","10:00"), ("14:00","14:30"), ("16:00","16:30")],
        "Austin":   [],  # free all day
        "Betty":    [("09:30","10:00"), ("11:30","12:00"), ("13:30","14:00"), ("16:00","16:30")],
        "Judith":   [("09:00","11:00"), ("12:00","13:00"), ("14:00","15:00")],
        "Terry":    [("09:30","10:00"), ("11:30","12:30"), ("13:00","14:00"), ("15:00","15:30"), ("16:00","17:00")],
        "Kathryn":  [("09:30","10:00"), ("10:30","11:00"), ("11:30","13:00"), ("14:00","16:00"), ("16:30","17:00")],
    }

    # Convert busy intervals to minutes and merge
    busy_minutes = {}
    for name, meetings in schedules.items():
        intervals = [(to_minutes(s), to_minutes(e)) for s, e in meetings]
        busy_minutes[name] = merge_intervals(intervals)

    # Compute free intervals within work hours for each participant
    all_free = []
    for name, busy in busy_minutes.items():
        free = invert_to_free(busy, work_start, work_end)
        all_free.append(free)

    start, end = find_meeting_slot(all_free, duration)
    if start == -1:
        raise SystemExit("No available slot found that meets all constraints.")

    print(f"{to_hhmm(start)}:{to_hhmm(end)}")
    print(day)

if __name__ == "__main__":
    main()