from typing import List, Tuple

def to_min(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_str(m: int) -> str:
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def crop_interval(interval: Tuple[int,int], bounds: Tuple[int,int]) -> Tuple[int,int] | None:
    s, e = interval
    b_s, b_e = bounds
    s, e = max(s, b_s), min(e, b_e)
    return (s, e) if s < e else None

def complement_within(busy: List[Tuple[int, int]], bounds: Tuple[int, int]) -> List[Tuple[int, int]]:
    b_s, b_e = bounds
    if b_s >= b_e:
        return []
    # Crop busy intervals to bounds and merge
    cropped = []
    for inter in busy:
        ci = crop_interval(inter, bounds)
        if ci:
            cropped.append(ci)
    busy_merged = merge_intervals(cropped)
    free = []
    prev = b_s
    for s, e in busy_merged:
        if prev < s:
            free.append((prev, s))
        prev = max(prev, e)
    if prev < b_e:
        free.append((prev, b_e))
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
    res = lists[0]
    for lst in lists[1:]:
        res = intersect_two(res, lst)
        if not res:
            break
    return res

def find_earliest_slot(free_intervals: List[Tuple[int,int]], duration: int) -> Tuple[int,int] | None:
    for s, e in free_intervals:
        if e - s >= duration:
            return (s, s + duration)
    return None

def main():
    day = "Monday"
    work_start = to_min("09:00")
    work_end = to_min("17:00")
    duration = 60  # minutes

    # Busy schedules (inclusive start, exclusive end semantics for calculation)
    ryan_busy = [
        (to_min("09:00"), to_min("09:30")),
        (to_min("12:30"), to_min("13:00")),
    ]
    ruth_busy = []  # no meetings
    denise_busy = [
        (to_min("09:30"), to_min("10:30")),
        (to_min("12:00"), to_min("13:00")),
        (to_min("14:30"), to_min("16:30")),
    ]

    # Base work bounds
    bounds = (work_start, work_end)

    # Preference/constraint: Denise does not want to meet on Monday after 12:30.
    # Interpret as meeting must end by 12:30 on Monday for Denise.
    denise_allowed_end = to_min("12:30")
    denise_bounds = (work_start, min(work_end, denise_allowed_end))

    # Compute free intervals within bounds
    ryan_free = complement_within(ryan_busy, bounds)
    ruth_free = complement_within(ruth_busy, bounds)
    denise_free = complement_within(denise_busy, denise_bounds)

    # Intersection of all participants' free intervals
    common_free = intersect_all([ryan_free, ruth_free, denise_free])

    # Find earliest slot of required duration
    slot = find_earliest_slot(common_free, duration)
    if not slot:
        raise SystemExit("No suitable slot found, despite problem statement indicating one exists.")

    start_str = to_str(slot[0])
    end_str = to_str(slot[1])

    # Output: include both the time range and the day of the week
    print(f"{day} {{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()