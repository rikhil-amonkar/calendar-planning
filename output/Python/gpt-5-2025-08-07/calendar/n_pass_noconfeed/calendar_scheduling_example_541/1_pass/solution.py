from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

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

def invert_intervals(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    free = []
    current = work_start
    for s, e in busy:
        if e <= current:
            continue
        if s > current:
            free.append((current, s))
        current = max(current, e)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def first_slot(intervals: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in intervals:
        if e - s >= duration:
            return (s, s + duration)
    return None

def main():
    day = "Monday"
    work_start_str, work_end_str = "09:00", "17:00"
    duration_min = 60

    work_start = to_minutes(work_start_str)
    work_end = to_minutes(work_end_str)

    participants_busy_str = {
        "Kayla": [("10:00", "10:30"), ("14:30", "16:00")],
        "Rebecca": [("09:00", "13:00"), ("13:30", "15:00"), ("15:30", "16:00")],
    }

    # Prepare busy intervals in minutes clipped to work hours and merged
    participants_free = []
    for person, blocks in participants_busy_str.items():
        busy = []
        for s_str, e_str in blocks:
            s, e = to_minutes(s_str), to_minutes(e_str)
            # Clip to work window
            s = max(s, work_start)
            e = min(e, work_end)
            if s < e:
                busy.append((s, e))
        busy = merge_intervals(busy)
        free = invert_intervals(busy, work_start, work_end)
        participants_free.append(free)

    # Compute common free time across all participants
    common_free = participants_free[0]
    for free in participants_free[1:]:
        common_free = intersect_intervals(common_free, free)

    slot = first_slot(common_free, duration_min)
    if not slot:
        raise RuntimeError("No available slot found, but one was expected.")

    start_str = to_hhmm(slot[0])
    end_str = to_hhmm(slot[1])

    # Output must include time range HH:MM:HH:MM and the day of the week
    print(f"{start_str}:{end_str} {day}")

if __name__ == "__main__":
    main()