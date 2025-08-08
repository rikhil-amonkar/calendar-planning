from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def invert_intervals(busy: List[Tuple[int, int]], day_start: int, day_end: int) -> List[Tuple[int, int]]:
    busy = sorted(busy)
    free = []
    current = day_start
    for s, e in busy:
        if e <= current:
            continue
        if s > current:
            free.append((current, s))
        current = max(current, e)
    if current < day_end:
        free.append((current, day_end))
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
    res = lists[0]
    for nxt in lists[1:]:
        res = intersect_two(res, nxt)
        if not res:
            break
    return res

def find_slot(common_free: List[Tuple[int, int]], duration_min: int) -> Tuple[int, int]:
    for s, e in common_free:
        if e - s >= duration_min:
            return s, s + duration_min
    raise ValueError("No suitable slot found")

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 60  # minutes

    # Busy schedules (inclusive of start, exclusive of end)
    james_busy = [
        (to_minutes("11:30"), to_minutes("12:00")),
        (to_minutes("14:30"), to_minutes("15:00")),
    ]
    john_busy = [
        (to_minutes("09:30"), to_minutes("11:00")),
        (to_minutes("11:30"), to_minutes("12:00")),
        (to_minutes("12:30"), to_minutes("13:30")),
        (to_minutes("14:30"), to_minutes("16:30")),
    ]

    # Compute free slots within work hours
    james_free = invert_intervals(james_busy, work_start, work_end)
    john_free = invert_intervals(john_busy, work_start, work_end)

    # Common free slots
    common_free = intersect_all([james_free, john_free])

    # Find the earliest slot that fits the duration
    start, end = find_slot(common_free, duration)

    # Output
    print(day)
    print(f"{{{to_hhmm(start)}:{to_hhmm(end)}}}")

if __name__ == "__main__":
    main()