from typing import List, Tuple

def parse_time(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def format_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def normalize_busy(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    # Clip busy intervals to within the work window and sort
    clipped = []
    for s, e in busy:
        if e <= start or s >= end:
            continue
        clipped.append((max(s, start), min(e, end)))
    clipped.sort()
    return clipped

def free_intervals(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    busy = normalize_busy(busy, start, end)
    free = []
    cur = start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    out = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            out.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return out

def earliest_slot(common_free: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in common_free:
        if e - s >= duration:
            return s, s + duration
    raise ValueError("No suitable slot found")

def main():
    day = "Monday"
    work_start = parse_time("09:00")
    work_end = parse_time("17:00")
    duration = 30  # minutes

    adam_busy_str = [("09:30", "10:00"), ("12:30", "13:00"), ("14:30", "15:00"), ("16:30", "17:00")]
    roy_busy_str = [("10:00", "11:00"), ("11:30", "13:00"), ("13:30", "14:30"), ("16:30", "17:00")]

    adam_busy = [(parse_time(s), parse_time(e)) for s, e in adam_busy_str]
    roy_busy = [(parse_time(s), parse_time(e)) for s, e in roy_busy_str]

    adam_free = free_intervals(adam_busy, work_start, work_end)
    roy_free = free_intervals(roy_busy, work_start, work_end)

    common_free = intersect_intervals(adam_free, roy_free)
    start, end = earliest_slot(common_free, duration)

    start_str = format_time(start)
    end_str = format_time(end)

    # Output must include both the time range in HH:MM:HH:MM format (inside braces) and the day of the week
    print(f"{day} {{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()