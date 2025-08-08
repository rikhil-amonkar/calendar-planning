from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.strip().split(":"))
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

def clip_intervals(intervals: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    clipped = []
    for s, e in intervals:
        cs, ce = max(s, start), min(e, end)
        if cs < ce:
            clipped.append((cs, ce))
    return clipped

def invert_intervals(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    if not busy:
        return [(start, end)]
    busy = merge_intervals(clip_intervals(busy, start, end))
    free = []
    cur = start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    result = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            result.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return result

def find_meeting_slot(common_free: List[Tuple[int, int]], duration: int) -> Tuple[int, int] or None:
    for s, e in common_free:
        if e - s >= duration:
            return (s, s + duration)
    return None

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    busy_by_person = {
        "Joe":       [("09:30", "10:00"), ("10:30", "11:00")],
        "Keith":     [("11:30", "12:00"), ("15:00", "15:30")],
        "Patricia":  [("09:00", "09:30"), ("13:00", "13:30")],
        "Nancy":     [("09:00", "11:00"), ("11:30", "16:30")],
        "Pamela":    [("09:00", "10:00"), ("10:30", "11:00"), ("11:30", "12:30"),
                      ("13:00", "14:00"), ("14:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")],
    }

    # Convert busy schedules to minutes and compute free intervals per person
    free_by_person = []
    for _, intervals in busy_by_person.items():
        busy_minutes = [(to_minutes(s), to_minutes(e)) for s, e in intervals]
        free = invert_intervals(busy_minutes, work_start, work_end)
        free_by_person.append(free)

    # Compute common free intervals
    common_free = free_by_person[0]
    for free in free_by_person[1:]:
        common_free = intersect_two(common_free, free)
        if not common_free:
            break

    slot = find_meeting_slot(common_free, duration)
    if slot is None:
        raise RuntimeError("No common slot found, but problem guarantees a solution.")
    start_str = to_hhmm(slot[0])
    end_str = to_hhmm(slot[1])

    print(day)
    print(f"{{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()