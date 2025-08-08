from typing import List, Tuple

def to_minutes(hhmm: str) -> int:
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

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

def subtract_busy_from_work(work: Tuple[int, int], busy_intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    # Returns list of free intervals within work after removing busy intervals
    ws, we = work
    busy = merge_intervals([(max(ws, s), min(we, e)) for s, e in busy_intervals if e > ws and s < we])
    free = []
    current_start = ws
    for s, e in busy:
        if s > current_start:
            free.append((current_start, s))
        current_start = max(current_start, e)
    if current_start < we:
        free.append((current_start, we))
    return free

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

def find_earliest_slot(common: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in common:
        if e - s >= duration:
            return s, s + duration
    return None

def main():
    day = "Monday"
    meeting_duration_min = 30
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    work_hours = (work_start, work_end)

    # Busy schedules
    eric_busy = []  # "Erichas no meetings the whole day."
    ashley_busy = [
        (to_minutes("10:00"), to_minutes("10:30")),
        (to_minutes("11:00"), to_minutes("12:00")),
        (to_minutes("12:30"), to_minutes("13:00")),
        (to_minutes("15:00"), to_minutes("16:00")),
    ]
    ronald_busy = [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("10:00"), to_minutes("11:30")),
        (to_minutes("12:30"), to_minutes("14:00")),
        (to_minutes("14:30"), to_minutes("17:00")),
    ]
    larry_busy = [
        (to_minutes("09:00"), to_minutes("12:00")),
        (to_minutes("13:00"), to_minutes("17:00")),
    ]

    # Compute free intervals within work hours for each participant
    eric_free = subtract_busy_from_work(work_hours, eric_busy)
    ashley_free = subtract_busy_from_work(work_hours, ashley_busy)
    ronald_free = subtract_busy_from_work(work_hours, ronald_busy)
    larry_free = subtract_busy_from_work(work_hours, larry_busy)

    # Intersect all free intervals
    common_free = eric_free
    for person_free in [ashley_free, ronald_free, larry_free]:
        common_free = intersect_interval_lists(common_free, person_free)

    slot = find_earliest_slot(common_free, meeting_duration_min)
    if not slot:
        raise RuntimeError("No suitable slot found, but problem statement guarantees a solution.")
    start, end = slot
    print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")

if __name__ == "__main__":
    main()