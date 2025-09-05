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

def free_from_busy(work_start: int, work_end: int, busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    # Normalize and clip busy intervals to the work window
    clipped = []
    for s, e in busy:
        if e <= work_start or s >= work_end:
            continue
        clipped.append((max(s, work_start), min(e, work_end)))
    busy_merged = merge_intervals(clipped)
    free = []
    cur = work_start
    for s, e in busy_merged:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < work_end:
        free.append((cur, work_end))
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

def find_meeting(free_lists: List[List[Tuple[int, int]]], duration: int) -> Tuple[int, int]:
    # Intersect all participants' free intervals
    common = free_lists[0][:]
    for fl in free_lists[1:]:
        common = intersect_intervals(common, fl)
        if not common:
            break
    # Find earliest slot that fits the duration
    for s, e in common:
        if e - s >= duration:
            return s, s + duration
    raise ValueError("No suitable slot found")

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 60  # minutes

    schedules = {
        "Olivia": [("12:30", "13:30"), ("14:30", "15:00"), ("16:30", "17:00")],
        "Anna":   [],  # no meetings
        "Virginia": [("09:00", "10:00"), ("11:30", "16:00"), ("16:30", "17:00")],
        "Paul": [("09:00", "09:30"), ("11:00", "11:30"), ("13:00", "14:00"),
                 ("14:30", "16:00"), ("16:30", "17:00")]
    }

    # Convert to minutes
    busy_minutes = {
        person: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
        for person, intervals in schedules.items()
    }

    # Compute free intervals for each participant
    free_lists = [
        free_from_busy(work_start, work_end, busy_minutes[person])
        for person in schedules
    ]

    start, end = find_meeting(free_lists, duration)
    start_str, end_str = to_hhmm(start), to_hhmm(end)

    # Output must include {HH:MM:HH:MM} and the day of the week
    print(f"{{{start_str}:{end_str}}}")
    print(day)

if __name__ == "__main__":
    main()