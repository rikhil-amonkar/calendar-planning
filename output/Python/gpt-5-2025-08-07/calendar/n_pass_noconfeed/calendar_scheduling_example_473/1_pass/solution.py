from typing import List, Tuple

def m(h: int, mi: int) -> int:
    return h * 60 + mi

def fmt(minutes: int) -> str:
    h = minutes // 60
    mi = minutes % 60
    return f"{h:02d}:{mi:02d}"

def subtract_busy_from_window(window: Tuple[int, int], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    start, end = window
    free = []
    cursor = start
    for b_start, b_end in sorted(busy):
        if b_end <= cursor or b_start >= end:
            continue
        if b_start > cursor:
            free.append((cursor, min(b_start, end)))
        cursor = max(cursor, b_end)
        if cursor >= end:
            break
    if cursor < end:
        free.append((cursor, end))
    return [(s, e) for s, e in free if e - s > 0]

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

def find_meeting():
    day = "Monday"
    work_window = (m(9, 0), m(17, 0))
    duration = 30  # minutes

    schedules = {
        "Gregory": [(m(9, 0), m(9, 30)), (m(11, 30), m(12, 0))],
        "Jonathan": [(m(9, 0), m(9, 30)), (m(12, 0), m(12, 30)), (m(13, 0), m(13, 30)), (m(15, 0), m(16, 0)), (m(16, 30), m(17, 0))],
        "Barbara": [(m(10, 0), m(10, 30)), (m(13, 30), m(14, 0))],
        "Jesse": [(m(10, 0), m(11, 0)), (m(12, 30), m(14, 30))],
        "Alan": [(m(9, 30), m(11, 0)), (m(11, 30), m(12, 30)), (m(13, 0), m(15, 30)), (m(16, 0), m(17, 0))],
        "Nicole": [(m(9, 0), m(10, 30)), (m(11, 30), m(12, 0)), (m(12, 30), m(13, 30)), (m(14, 0), m(17, 0))],
        "Catherine": [(m(9, 0), m(10, 30)), (m(12, 0), m(13, 30)), (m(15, 0), m(15, 30)), (m(16, 0), m(16, 30))],
    }

    # Compute per-person free intervals within the work window
    free_by_person = []
    for busy in schedules.values():
        free = subtract_busy_from_window(work_window, busy)
        free_by_person.append(free)

    # Intersect all free intervals to get common availability
    common = [work_window]
    for free in free_by_person:
        common = intersect_intervals(common, free)
        if not common:
            break

    # Find earliest slot of required duration
    for s, e in common:
        if e - s >= duration:
            start = s
            end = s + duration
            print(f"{{{fmt(start)}:{fmt(end)}}} {day}")
            return

if __name__ == "__main__":
    find_meeting()