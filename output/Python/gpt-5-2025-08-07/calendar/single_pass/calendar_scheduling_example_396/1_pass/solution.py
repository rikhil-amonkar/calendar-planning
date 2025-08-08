from typing import List, Tuple

def parse_time(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

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

def invert_intervals(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    """Return free intervals within [start, end) given busy intervals."""
    if not busy:
        return [(start, end)]
    free = []
    cur = start
    for b_s, b_e in busy:
        if b_e <= cur:
            continue
        if b_s > cur:
            free.append((cur, min(b_s, end)))
        cur = max(cur, b_e)
        if cur >= end:
            break
    if cur < end:
        free.append((cur, end))
    return [(s, e) for s, e in free if e > s]

def intersect_interval_lists(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def find_meeting():
    day = "Monday"
    work_start, work_end = parse_time("09:00"), parse_time("17:00")
    duration = 30  # minutes

    schedules = {
        "Andrea": [],  # wide open
        "Jack": [("09:00", "09:30"), ("14:00", "14:30")],
        "Madison": [("09:30", "10:30"), ("13:00", "14:00"), ("15:00", "15:30"), ("16:30", "17:00")],
        "Rachel": [("09:30", "10:30"), ("11:00", "11:30"), ("12:00", "13:30"), ("14:30", "15:30"), ("16:00", "17:00")],
        "Douglas": [("09:00", "11:30"), ("12:00", "16:30")],
        "Ryan": [("09:00", "09:30"), ("13:00", "14:00"), ("14:30", "17:00")],
    }

    # Convert and clamp busy intervals to work hours, then merge
    busy_by_person = {}
    for person, intervals in schedules.items():
        mins = []
        for s, e in intervals:
            ms, me = parse_time(s), parse_time(e)
            if me <= work_start or ms >= work_end:
                continue
            ms = max(ms, work_start)
            me = min(me, work_end)
            if ms < me:
                mins.append((ms, me))
        busy_by_person[person] = merge_intervals(mins)

    # Compute free intervals for each person
    free_by_person = {
        p: invert_intervals(busy, work_start, work_end) for p, busy in busy_by_person.items()
    }

    # Intersect all free intervals
    common_free = [(work_start, work_end)]
    for p in schedules.keys():
        common_free = intersect_interval_lists(common_free, free_by_person[p])
        if not common_free:
            break

    # Find earliest slot of required duration
    meeting_start = meeting_end = None
    for s, e in common_free:
        if e - s >= duration:
            meeting_start = s
            meeting_end = s + duration
            break

    if meeting_start is None:
        raise RuntimeError("No feasible meeting time found, but a solution was expected.")

    time_range = f"{fmt_time(meeting_start)}:{fmt_time(meeting_end)}"
    print(f"{{{time_range}}}")
    print(day)

if __name__ == "__main__":
    find_meeting()