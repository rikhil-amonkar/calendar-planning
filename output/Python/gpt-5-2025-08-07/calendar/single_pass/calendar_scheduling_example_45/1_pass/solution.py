from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def from_minutes(m: int) -> str:
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

def clip_interval(interval: Tuple[int, int], bounds: Tuple[int, int]) -> Tuple[int, int] | None:
    s, e = interval
    bs, be = bounds
    s = max(s, bs)
    e = min(e, be)
    return (s, e) if s < e else None

def complement_intervals(busy: List[Tuple[int, int]], bounds: Tuple[int, int]) -> List[Tuple[int, int]]:
    bs, be = bounds
    if bs >= be:
        return []
    # Clip and merge busy intervals within bounds
    clipped = []
    for s, e in busy:
        c = clip_interval((s, e), (bs, be))
        if c:
            clipped.append(c)
    merged = merge_intervals(clipped)
    # Build complement
    free = []
    prev_end = bs
    for s, e in merged:
        if prev_end < s:
            free.append((prev_end, s))
        prev_end = max(prev_end, e)
    if prev_end < be:
        free.append((prev_end, be))
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

def earliest_slot(avails: List[Tuple[int, int]], duration: int) -> Tuple[int, int] | None:
    for s, e in avails:
        if e - s >= duration:
            return (s, s + duration)
    return None

def main():
    day = "Monday"
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    work_bounds = (work_start, work_end)
    duration = 30  # minutes

    # Busy schedules
    andrew_busy = []  # wide open
    grace_busy = []   # no meetings
    samuel_busy_str = [
        ("09:00", "10:30"),
        ("11:30", "12:00"),
        ("13:00", "13:30"),
        ("14:00", "16:00"),
        ("16:30", "17:00"),
    ]
    samuel_busy = [(to_minutes(s), to_minutes(e)) for s, e in samuel_busy_str]

    # Compute free intervals for each participant
    andrew_free = complement_intervals(andrew_busy, work_bounds)
    grace_free = complement_intervals(grace_busy, work_bounds)
    samuel_free = complement_intervals(samuel_busy, work_bounds)

    # Intersect all participants' free intervals
    group_free = intersect_two(andrew_free, grace_free)
    group_free = intersect_two(group_free, samuel_free)

    # Find earliest available slot
    slot = earliest_slot(group_free, duration)
    if not slot:
        raise RuntimeError("No available slot found, but a solution was expected.")
    start, end = slot
    time_braced = "{" + from_minutes(start) + ":" + from_minutes(end) + "}"
    print(f"{day} {time_braced}")

if __name__ == "__main__":
    main()