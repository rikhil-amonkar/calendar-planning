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

def clip_intervals(intervals: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    clipped = []
    for s, e in intervals:
        s2, e2 = max(s, start), min(e, end)
        if s2 < e2:
            clipped.append((s2, e2))
    return merge_intervals(clipped)

def invert_intervals(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    busy = merge_intervals(clip_intervals(busy, start, end))
    free = []
    cursor = start
    for s, e in busy:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < end:
        free.append((cursor, end))
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
    for lst in lists[1:]:
        res = intersect_two(res, lst)
        if not res:
            break
    return res

def find_slot(common_free: List[Tuple[int, int]], duration: int, prefer_end: int = None) -> Tuple[int, int]:
    # First, try to satisfy preference: meeting ends by prefer_end
    if prefer_end is not None:
        for s, e in common_free:
            if s <= prefer_end - duration and s + duration <= e:
                return s, s + duration
    # Otherwise, pick the earliest available
    for s, e in common_free:
        if s + duration <= e:
            return s, s + duration
    raise ValueError("No suitable slot found")

def main():
    day = "Monday"
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    duration = 30  # minutes
    prefer_avoid_after = to_minutes("15:00")  # Bobby prefers before this time

    # Busy schedules
    lisa_busy_str = [("09:00","10:00"), ("10:30","11:30"), ("12:30","13:00"), ("16:00","16:30")]
    bobby_busy_str = [("09:00","09:30"), ("10:00","10:30"), ("11:30","12:00"), ("15:00","15:30")]
    randy_busy_str = [("09:30","10:00"), ("10:30","11:00"), ("11:30","12:30"), ("13:00","13:30"), ("14:30","15:30"), ("16:00","16:30")]

    def parse_list(lst): 
        return [(to_minutes(s), to_minutes(e)) for s, e in lst]

    lisa_busy = parse_list(lisa_busy_str)
    bobby_busy = parse_list(bobby_busy_str)
    randy_busy = parse_list(randy_busy_str)

    # Compute free intervals within work hours
    lisa_free = invert_intervals(lisa_busy, work_start, work_end)
    bobby_free = invert_intervals(bobby_busy, work_start, work_end)
    randy_free = invert_intervals(randy_busy, work_start, work_end)

    # Common free time
    common_free = intersect_all([lisa_free, bobby_free, randy_free])

    # Find a slot honoring preference if possible
    start, end = find_slot(common_free, duration, prefer_end=prefer_avoid_after)

    # Output in required format
    print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")

if __name__ == "__main__":
    main()