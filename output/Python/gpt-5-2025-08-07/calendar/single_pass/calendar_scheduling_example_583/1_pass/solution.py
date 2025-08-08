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

def invert_to_free(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    busy = merge_intervals([(max(work_start, s), min(work_end, e)) for s, e in busy if e > work_start and s < work_end])
    free = []
    cur = work_start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < work_end:
        free.append((cur, work_end))
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

def earliest_slot(free_blocks: List[List[Tuple[int, int]]], duration: int) -> Tuple[int, int]:
    # Intersect all participants' free times
    common = free_blocks[0]
    for fb in free_blocks[1:]:
        common = intersect(common, fb)
    # Find earliest interval with enough duration
    for s, e in common:
        if e - s >= duration:
            return s, s + duration
    raise ValueError("No suitable slot found")

def main():
    day = "Monday"
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    duration = 30  # minutes

    # Busy schedules for Monday
    lisa_busy = [
        ("09:00", "09:30"),
        ("10:30", "11:00"),
        ("14:00", "16:00"),
    ]
    anthony_busy = [
        ("09:00", "09:30"),
        ("11:00", "11:30"),
        ("12:30", "13:30"),
        ("14:00", "15:00"),
        ("15:30", "16:00"),
        ("16:30", "17:00"),
    ]

    lisa_busy_m = [(to_minutes(s), to_minutes(e)) for s, e in lisa_busy]
    anthony_busy_m = [(to_minutes(s), to_minutes(e)) for s, e in anthony_busy]

    lisa_free = invert_to_free(lisa_busy_m, work_start, work_end)
    anthony_free = invert_to_free(anthony_busy_m, work_start, work_end)

    start, end = earliest_slot([lisa_free, anthony_free], duration)
    start_str, end_str = to_hhmm(start), to_hhmm(end)

    # Output: time range in HH:MM:HH:MM format (wrapped in braces as example suggests) and the day
    print(f"{{{start_str}:{end_str}}}")
    print(day)

if __name__ == "__main__":
    main()