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

def subtract_from_window(window: Tuple[int,int], blocks: List[Tuple[int,int]]) -> List[Tuple[int,int]]:
    ws, we = window
    blocks = [(max(ws, s), min(we, e)) for s, e in blocks if e > ws and s < we]
    blocks = merge_intervals(blocks)
    free = []
    cur = ws
    for s, e in blocks:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < we:
        free.append((cur, we))
    return free

def intersect_two(a: List[Tuple[int,int]], b: List[Tuple[int,int]]) -> List[Tuple[int,int]]:
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

def intersect_all(lists: List[List[Tuple[int,int]]]) -> List[Tuple[int,int]]:
    if not lists:
        return []
    inter = lists[0]
    for lst in lists[1:]:
        inter = intersect_two(inter, lst)
        if not inter:
            break
    return inter

def find_slot(common_free: List[Tuple[int,int]], duration: int) -> Tuple[int,int]:
    for s, e in common_free:
        if e - s >= duration:
            return (s, s + duration)
    return None

def main():
    day = "Monday"
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    window = (work_start, work_end)
    duration = 30  # minutes

    busy_str = {
        "John": [("11:30","12:00"), ("14:00","14:30")],
        "Megan": [("12:00","12:30"), ("14:00","15:00"), ("15:30","16:00")],
        "Brandon": [],
        "Kimberly": [("09:00","09:30"), ("10:00","10:30"), ("11:00","14:30"), ("15:00","16:00"), ("16:30","17:00")],
        "Sean": [("10:00","11:00"), ("11:30","14:00"), ("15:00","15:30")],
        "Lori": [("09:00","09:30"), ("10:30","12:00"), ("13:00","14:30"), ("16:00","16:30")],
    }

    busy = {
        person: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
        for person, intervals in busy_str.items()
    }

    free_all = [
        subtract_from_window(window, merge_intervals(busy[person]))
        for person in busy
    ]

    common_free = intersect_all(free_all)
    slot = find_slot(common_free, duration)

    if slot is None:
        raise SystemExit("No available slot found.")
    start, end = slot
    print(f"{to_hhmm(start)}:{to_hhmm(end)}")
    print(day)

if __name__ == "__main__":
    main()