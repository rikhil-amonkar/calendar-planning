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

def invert_intervals(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    free = []
    cursor = work_start
    for s, e in busy:
        if e <= work_start or s >= work_end:
            continue
        s = max(s, work_start)
        e = min(e, work_end)
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < work_end:
        free.append((cursor, work_end))
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

def find_meeting_slot(free_sets: List[List[Tuple[int, int]]], duration: int) -> Tuple[int, int]:
    common = free_sets[0]
    for fs in free_sets[1:]:
        common = intersect_two(common, fs)
        if not common:
            return (-1, -1)
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
        "Patrick": [("09:00","09:30"), ("10:00","10:30"), ("13:30","14:00"), ("16:00","16:30")],
        "Kayla":   [("12:30","13:30"), ("15:00","15:30"), ("16:00","16:30")],
        "Carl":    [("10:30","11:00"), ("12:00","12:30"), ("13:00","13:30"), ("14:30","17:00")],
        "Christian":[("09:00","12:30"), ("13:00","14:00"), ("14:30","17:00")],
    }

    # Convert to minutes and merge busy intervals
    busy_minutes = {}
    for person, intervals in schedules.items():
        mins = [(to_minutes(s), to_minutes(e)) for s, e in intervals]
        busy_minutes[person] = merge_intervals(mins)

    # Compute free intervals within work hours
    free_sets = []
    for person in schedules.keys():
        free_sets.append(invert_intervals(busy_minutes[person], work_start, work_end))

    # Find earliest slot
    start, end = find_meeting_slot(free_sets, duration)
    if start == -1:
        raise SystemExit("No available time slot found.")

    time_range_str = f"{{{to_hhmm(start)}:{to_hhmm(end)}}}"
    print(time_range_str)
    print(day)

if __name__ == "__main__":
    main()