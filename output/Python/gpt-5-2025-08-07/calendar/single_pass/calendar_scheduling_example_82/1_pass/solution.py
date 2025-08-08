from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def normalize_and_clip(busy: List[Tuple[int, int]], day_start: int, day_end: int) -> List[Tuple[int, int]]:
    # Clip to work hours and merge overlaps
    clipped = []
    for s, e in busy:
        s = max(s, day_start)
        e = min(e, day_end)
        if s < e:
            clipped.append((s, e))
    clipped.sort()
    merged = []
    for s, e in clipped:
        if not merged or s > merged[-1][1]:
            merged.append((s, e))
        else:
            merged[-1] = (merged[-1][0], max(merged[-1][1], e))
    return merged

def free_intervals(busy: List[Tuple[int, int]], day_start: int, day_end: int) -> List[Tuple[int, int]]:
    busy = normalize_and_clip(busy, day_start, day_end)
    free = []
    cur = day_start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < day_end:
        free.append((cur, day_end))
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

def find_earliest_slot(free_lists: List[List[Tuple[int, int]]], duration: int) -> Tuple[int, int]:
    # Intersect all free lists
    if not free_lists:
        return (-1, -1)
    common = free_lists[0]
    for fl in free_lists[1:]:
        common = intersect(common, fl)
        if not common:
            return (-1, -1)
    # Find earliest interval with sufficient length
    for s, e in common:
        if e - s >= duration:
            return (s, s + duration)
    return (-1, -1)

def main():
    day = "Monday"
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    duration = 30  # minutes

    schedules = {
        "Michael": [("09:30", "10:30"), ("15:00", "15:30"), ("16:00", "16:30")],
        "Eric": [],
        "Arthur": [("09:00", "12:00"), ("13:00", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")],
    }

    # Convert to minutes
    busy_minutes = {
        person: [(to_minutes(s), to_minutes(e)) for s, e in slots]
        for person, slots in schedules.items()
    }

    # Compute free intervals within working hours for each participant
    free_lists = [
        free_intervals(busy_minutes[person], work_start, work_end)
        for person in schedules
    ]

    start, end = find_earliest_slot(free_lists, duration)
    if start == -1:
        raise RuntimeError("No available meeting slot found.")

    # Output: day of week and HH:MM:HH:MM
    print(day)
    print(f"{to_hhmm(start)}:{to_hhmm(end)}")

if __name__ == "__main__":
    main()