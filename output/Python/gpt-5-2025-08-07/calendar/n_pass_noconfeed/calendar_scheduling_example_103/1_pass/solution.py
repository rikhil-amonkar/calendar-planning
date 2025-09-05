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
    busy = merge_intervals([ (max(work_start, s), min(work_end, e)) for s, e in busy if e > work_start and s < work_end ])
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

def find_slot(common_free: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in common_free:
        if e - s >= duration:
            return s, s + duration
    raise ValueError("No suitable slot found")

def main():
    day = "Monday"
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    duration = 30  # minutes

    # Busy schedules on Monday
    diane_busy = [(to_minutes("09:30"), to_minutes("10:00")),
                  (to_minutes("14:30"), to_minutes("15:00"))]
    jack_busy = [(to_minutes("13:30"), to_minutes("14:00")),
                 (to_minutes("14:30"), to_minutes("15:00"))]
    eugene_busy = [(to_minutes("09:00"), to_minutes("10:00")),
                   (to_minutes("10:30"), to_minutes("11:30")),
                   (to_minutes("12:00"), to_minutes("14:30")),
                   (to_minutes("15:00"), to_minutes("16:30"))]
    patricia_busy = [(to_minutes("09:30"), to_minutes("10:30")),
                     (to_minutes("11:00"), to_minutes("12:00")),
                     (to_minutes("12:30"), to_minutes("14:00")),
                     (to_minutes("15:00"), to_minutes("16:30"))]

    # Compute free intervals
    diane_free = invert_intervals(diane_busy, work_start, work_end)
    jack_free = invert_intervals(jack_busy, work_start, work_end)
    eugene_free = invert_intervals(eugene_busy, work_start, work_end)
    patricia_free = invert_intervals(patricia_busy, work_start, work_end)

    # Intersection of all free intervals
    common = intersect(diane_free, jack_free)
    common = intersect(common, eugene_free)
    common = intersect(common, patricia_free)

    start, end = find_slot(common, duration)
    time_range = f"{to_hhmm(start)}:{to_hhmm(end)}"
    print(f"{day} {{{time_range}}}")

if __name__ == "__main__":
    main()