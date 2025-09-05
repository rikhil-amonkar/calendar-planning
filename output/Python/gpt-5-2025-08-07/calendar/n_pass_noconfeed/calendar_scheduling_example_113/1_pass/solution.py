from typing import List, Tuple

def hm(s: str) -> int:
    h, m = map(int, s.split(":"))
    return h * 60 + m

def fmt(minutes: int) -> str:
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

def clip_intervals(intervals: List[Tuple[int, int]], ws: int, we: int) -> List[Tuple[int, int]]:
    clipped = []
    for s, e in intervals:
        if e <= ws or s >= we:
            continue
        clipped.append((max(s, ws), min(e, we)))
    return clipped

def invert_to_free(busy: List[Tuple[int, int]], ws: int, we: int) -> List[Tuple[int, int]]:
    busy = merge_intervals(clip_intervals(busy, ws, we))
    free = []
    curr = ws
    for s, e in busy:
        if curr < s:
            free.append((curr, s))
        curr = max(curr, e)
    if curr < we:
        free.append((curr, we))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def first_slot(common_free: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in common_free:
        if e - s >= duration:
            return (s, s + duration)
    raise ValueError("No suitable slot found")

def main():
    day = "Monday"
    work_start, work_end = hm("09:00"), hm("17:00")
    duration = 30  # minutes

    schedules = {
        "Bradley": [("09:30", "10:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("15:30", "16:00")],
        "Teresa": [("10:30", "11:00"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "15:00")],
        "Elizabeth": [("09:00", "09:30"), ("10:30", "11:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("15:30", "17:00")],
        "Christian": [("09:00", "09:30"), ("10:30", "17:00")],
    }

    # Convert to minutes and compute free intervals for each participant
    free_lists = []
    for person, busy_str in schedules.items():
        busy = [(hm(s), hm(e)) for s, e in busy_str]
        free = invert_to_free(busy, work_start, work_end)
        free_lists.append(free)

    # Intersect all free intervals
    common = free_lists[0]
    for fl in free_lists[1:]:
        common = intersect_two(common, fl)

    start, end = first_slot(common, duration)

    # Output in required formats
    print(f"{{{fmt(start)}:{fmt(end)}}}")
    print(day)

if __name__ == "__main__":
    main()