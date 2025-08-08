from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

def invert_busy_to_free(work_window: Tuple[int, int], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    ws, we = work_window
    # Normalize and clip busy times to work window
    clipped = []
    for s, e in sorted(busy):
        s = max(s, ws)
        e = min(e, we)
        if s < e:
            clipped.append((s, e))
    # Build free intervals
    free = []
    cursor = ws
    for s, e in clipped:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < we:
        free.append((cursor, we))
    return free

def intersect_intervals(a: List[Tuple[int,int]], b: List[Tuple[int,int]]) -> List[Tuple[int,int]]:
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

def find_meeting_slot(free_lists: List[List[Tuple[int,int]]], duration: int) -> Tuple[int, int]:
    # Intersect all free intervals
    common = free_lists[0]
    for lst in free_lists[1:]:
        common = intersect_intervals(common, lst)
        if not common:
            return None
    # Find earliest slot with required duration
    for s, e in common:
        if e - s >= duration:
            return s, s + duration
    return None

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    work_window = (work_start, work_end)
    duration = 60  # minutes

    schedules = {
        "Stephanie": [("10:00","10:30"), ("16:00","16:30")],
        "Cheryl":    [("10:00","10:30"), ("11:30","12:00"), ("13:30","14:00"), ("16:30","17:00")],
        "Bradley":   [("09:30","10:00"), ("10:30","11:30"), ("13:30","14:00"), ("14:30","15:00"), ("15:30","17:00")],
        "Steven":    [("09:00","12:00"), ("13:00","13:30"), ("14:30","17:00")],
    }

    # Convert schedules to minutes
    busy_minutes = {
        person: [(to_minutes(s), to_minutes(e)) for s, e in slots]
        for person, slots in schedules.items()
    }

    # Compute free time for each participant within work hours
    free_lists = [
        invert_busy_to_free(work_window, busy_minutes[person])
        for person in schedules
    ]

    # Find a common slot
    slot = find_meeting_slot(free_lists, duration)
    if not slot:
        print(f"{day} {{No available slot}}")
        return

    start, end = slot
    time_range = f"{to_hhmm(start)}:{to_hhmm(end)}"
    # Output must include the time range in HH:MM:HH:MM and the day of the week
    print(f"{day} {{{time_range}}}")

if __name__ == "__main__":
    main()