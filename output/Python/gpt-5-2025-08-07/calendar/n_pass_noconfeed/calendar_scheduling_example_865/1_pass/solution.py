from typing import List, Tuple, Dict

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_str(m: int) -> str:
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

def clamp_to_workday(intervals: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    clamped = []
    for s, e in intervals:
        s = max(s, work_start)
        e = min(e, work_end)
        if s < e:
            clamped.append((s, e))
    return clamped

def free_from_busy(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    busy = clamp_to_workday(merge_intervals(busy), work_start, work_end)
    free = []
    cur = work_start
    for s, e in busy:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < work_end:
        free.append((cur, work_end))
    return free

def intersect(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def earliest_slot(common_free: List[Tuple[int, int]], duration: int) -> Tuple[int, int] | None:
    for s, e in common_free:
        if e - s >= duration:
            return (s, s + duration)
    return None

def main():
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    duration = 60  # minutes

    megan: Dict[str, List[Tuple[str, str]]] = {
        "Monday":    [("13:00","13:30"), ("14:00","15:30")],
        "Tuesday":   [("09:00","09:30"), ("12:00","12:30"), ("16:00","17:00")],
        "Wednesday": [("09:30","10:00"), ("10:30","11:30"), ("12:30","14:00"), ("16:00","16:30")],
        "Thursday":  [("13:30","14:30"), ("15:00","15:30")],
    }
    daniel: Dict[str, List[Tuple[str, str]]] = {
        "Monday":    [("10:00","11:30"), ("12:30","15:00")],
        "Tuesday":   [("09:00","10:00"), ("10:30","17:00")],
        "Wednesday": [("09:00","10:00"), ("10:30","11:30"), ("12:00","17:00")],
        "Thursday":  [("09:00","12:00"), ("12:30","14:30"), ("15:00","15:30"), ("16:00","17:00")],
    }

    # Convert to minutes
    megan_m = {d: [(to_minutes(s), to_minutes(e)) for s, e in megan.get(d, [])] for d in days}
    daniel_m = {d: [(to_minutes(s), to_minutes(e)) for s, e in daniel.get(d, [])] for d in days}

    for day in days:
        megan_free = free_from_busy(megan_m.get(day, []), work_start, work_end)
        daniel_free = free_from_busy(daniel_m.get(day, []), work_start, work_end)
        common = intersect(megan_free, daniel_free)
        slot = earliest_slot(common, duration)
        if slot:
            start_str, end_str = to_str(slot[0]), to_str(slot[1])
            print(day)
            print(f"{{{start_str}:{end_str}}}")
            return

if __name__ == "__main__":
    main()