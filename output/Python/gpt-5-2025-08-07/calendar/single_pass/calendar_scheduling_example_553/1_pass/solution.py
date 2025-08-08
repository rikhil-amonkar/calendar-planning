from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def from_minutes(m: int) -> str:
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

def subtract_intervals(base: List[Tuple[int, int]], blocks: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    # Subtract each block from the base intervals
    blocks = merge_intervals(blocks)
    free = []
    for bs, be in base:
        curr = [(bs, be)]
        for s, e in blocks:
            nxt = []
            for cs, ce in curr:
                if e <= cs or s >= ce:
                    # no overlap
                    nxt.append((cs, ce))
                else:
                    # overlap exists
                    if s > cs:
                        nxt.append((cs, s))
                    if e < ce:
                        nxt.append((e, ce))
            curr = nxt
        free.extend(curr)
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

def earliest_slot(intervals: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in intervals:
        if e - s >= duration:
            return s, s + duration
    return None

def earliest_slot_with_end_by(intervals: List[Tuple[int, int]], duration: int, end_by: int) -> Tuple[int, int]:
    # Find earliest slot that fully ends by `end_by`
    for s, e in intervals:
        if s <= end_by - duration and e - s >= duration:
            return s, s + duration
    return None

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    meeting_duration = 30  # minutes

    # Busy schedules (inclusive of day constraints)
    eric_busy = [
        (to_minutes("12:00"), to_minutes("13:00")),
        (to_minutes("14:00"), to_minutes("15:00")),
    ]
    henry_busy = [
        (to_minutes("09:30"), to_minutes("10:00")),
        (to_minutes("10:30"), to_minutes("11:00")),
        (to_minutes("11:30"), to_minutes("12:30")),
        (to_minutes("13:00"), to_minutes("13:30")),
        (to_minutes("14:30"), to_minutes("15:00")),
        (to_minutes("16:00"), to_minutes("17:00")),
    ]

    # Working window
    work_window = [(work_start, work_end)]

    # Compute free intervals for each participant
    eric_free = subtract_intervals(work_window, eric_busy)
    henry_free = subtract_intervals(work_window, henry_busy)

    # Common free intervals
    common_free = intersect_interval_lists(eric_free, henry_free)

    # Preference: Henry would rather not meet on Monday after 10:00.
    prefer_end_by = to_minutes("10:00")
    slot = earliest_slot_with_end_by(common_free, meeting_duration, prefer_end_by)

    # If no preferred slot, pick the earliest general slot
    if slot is None:
        slot = earliest_slot(common_free, meeting_duration)

    if slot is None:
        raise RuntimeError("No available slot found, but problem statement guarantees a solution.")

    start, end = slot
    time_range = f"{from_minutes(start)}:{from_minutes(end)}"

    print(time_range)
    print(day)

if __name__ == "__main__":
    main()