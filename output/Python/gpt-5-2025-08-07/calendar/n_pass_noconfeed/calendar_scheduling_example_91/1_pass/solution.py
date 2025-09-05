from typing import List, Tuple

def time_to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m: int) -> str:
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

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

def clamp_intervals_to_workday(intervals: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    clamped = []
    for s, e in intervals:
        s = max(s, work_start)
        e = min(e, work_end)
        if s < e:
            clamped.append((s, e))
    return clamped

def compute_free_intervals(work_start: int, work_end: int, busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    busy = merge_intervals(clamp_intervals_to_workday(busy, work_start, work_end))
    free = []
    cursor = work_start
    for s, e in busy:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < work_end:
        free.append((cursor, work_end))
    return free

def intersect_interval_lists(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    result = []
    while i < len(a) and j < len(b):
        s1, e1 = a[i]
        s2, e2 = b[j]
        start = max(s1, s2)
        end = min(e1, e2)
        if start < end:
            result.append((start, end))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return result

def find_slot(common_free: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in common_free:
        if e - s >= duration:
            return (s, s + duration)
    raise ValueError("No valid slot found")

def main():
    day = "Monday"
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    duration = 60  # minutes

    schedules = {
        "Danielle": [("09:00","10:00"), ("10:30","11:00"), ("14:30","15:00"), ("15:30","16:00"), ("16:30","17:00")],
        "Bruce":    [("11:00","11:30"), ("12:30","13:00"), ("14:00","14:30"), ("15:30","16:00")],
        "Eric":     [("09:00","09:30"), ("10:00","11:00"), ("11:30","13:00"), ("14:30","15:30")],
    }

    busy_minutes = {p: [(time_to_minutes(s), time_to_minutes(e)) for s, e in slots] for p, slots in schedules.items()}
    free_intervals = {p: compute_free_intervals(work_start, work_end, busy_minutes[p]) for p in schedules}

    # Intersect all participants' free intervals
    participants = list(free_intervals.keys())
    common_free = free_intervals[participants[0]]
    for p in participants[1:]:
        common_free = intersect_interval_lists(common_free, free_intervals[p])

    start, end = find_slot(common_free, duration)

    # Output format: Day {HH:MM:HH:MM}
    print(f"{day} {{{minutes_to_time(start)}:{minutes_to_time(end)}}}")

if __name__ == "__main__":
    main()