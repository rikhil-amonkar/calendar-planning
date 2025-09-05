from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

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

def invert_intervals(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    busy = merge_intervals([(max(work_start, s), min(work_end, e)) for s, e in busy if e > work_start and s < work_end])
    free = []
    cursor = work_start
    for s, e in busy:
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

def intersect_all(interval_lists: List[List[Tuple[int, int]]]) -> List[Tuple[int, int]]:
    if not interval_lists:
        return []
    inter = interval_lists[0]
    for lst in interval_lists[1:]:
        inter = intersect_two(inter, lst)
        if not inter:
            break
    return inter

def find_slot(free_intersections: List[Tuple[int, int]], duration_min: int) -> Tuple[int, int]:
    for s, e in free_intersections:
        if e - s >= duration_min:
            return s, s + duration_min
    raise ValueError("No suitable slot found")

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration_min = 30

    # Busy schedules on Monday
    schedules = {
        "Eric": [],  # Free all day
        "Ashley": [
            (to_minutes("10:00"), to_minutes("10:30")),
            (to_minutes("11:00"), to_minutes("12:00")),
            (to_minutes("12:30"), to_minutes("13:00")),
            (to_minutes("15:00"), to_minutes("16:00")),
        ],
        "Ronald": [
            (to_minutes("09:00"), to_minutes("09:30")),
            (to_minutes("10:00"), to_minutes("11:30")),
            (to_minutes("12:30"), to_minutes("14:00")),
            (to_minutes("14:30"), to_minutes("17:00")),
        ],
        "Larry": [
            (to_minutes("09:00"), to_minutes("12:00")),
            (to_minutes("13:00"), to_minutes("17:00")),
        ],
    }

    free_lists = [
        invert_intervals(schedules[name], work_start, work_end) for name in schedules
    ]
    common_free = intersect_all(free_lists)
    start, end = find_slot(common_free, duration_min)

    print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")

if __name__ == "__main__":
    main()