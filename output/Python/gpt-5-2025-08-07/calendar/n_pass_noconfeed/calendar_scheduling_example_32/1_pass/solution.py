from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

def complement(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    start, end = window
    if start >= end:
        return []
    busy_sorted = sorted([b for b in busy if b[1] > start and b[0] < end])
    free = []
    cur = start
    for s, e in busy_sorted:
        s = max(s, start)
        e = min(e, end)
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i, j = 0, 0
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

def find_slot(common_free: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in common_free:
        if e - s >= duration:
            return s, s + duration
    raise ValueError("No suitable slot found")

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    # Busy schedules (start, end) for Monday
    emily_busy = [
        ("10:00", "10:30"),
        ("11:30", "12:30"),
        ("14:00", "15:00"),
        ("16:00", "16:30"),
    ]
    melissa_busy = [
        ("09:30", "10:00"),
        ("14:30", "15:00"),
    ]
    frank_busy = [
        ("10:00", "10:30"),
        ("11:00", "11:30"),
        ("12:30", "13:00"),
        ("13:30", "14:30"),
        ("15:00", "16:00"),
        ("16:30", "17:00"),
    ]

    # Convert to minutes
    emily_busy_m = [(to_minutes(s), to_minutes(e)) for s, e in emily_busy]
    melissa_busy_m = [(to_minutes(s), to_minutes(e)) for s, e in melissa_busy]
    frank_busy_m = [(to_minutes(s), to_minutes(e)) for s, e in frank_busy]

    # Frank does not want to meet after 09:30 on Monday => constrain his day window to end at 09:30
    frank_preference_end = to_minutes("09:30")

    emily_free = complement(emily_busy_m, (work_start, work_end))
    melissa_free = complement(melissa_busy_m, (work_start, work_end))
    frank_free = complement(frank_busy_m, (work_start, min(work_end, frank_preference_end)))

    # Intersect free times
    common = intersect_intervals(emily_free, melissa_free)
    common = intersect_intervals(common, frank_free)

    start, end = find_slot(common, duration)
    print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")

if __name__ == "__main__":
    main()