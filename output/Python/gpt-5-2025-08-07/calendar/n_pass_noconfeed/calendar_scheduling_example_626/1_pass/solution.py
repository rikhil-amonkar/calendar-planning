from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
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

def clamp_and_free(work_start: int, work_end: int, busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    # Clamp busy intervals to work hours and merge overlaps
    clamped = []
    for s, e in busy:
        if e <= work_start or s >= work_end:
            continue
        clamped.append((max(s, work_start), min(e, work_end)))
    clamped = merge_intervals(clamped)

    # Compute free intervals within work window
    free = []
    curr = work_start
    for s, e in clamped:
        if s > curr:
            free.append((curr, s))
        curr = max(curr, e)
    if curr < work_end:
        free.append((curr, work_end))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    inter = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            inter.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return inter

# Input data for the task
work_hours = {"Monday": ("09:00", "17:00"), "Tuesday": ("09:00", "17:00")}
duration_min = 60  # 1 hour

patricia_busy = {
    "Monday": [("10:00", "10:30"), ("11:30", "12:00"), ("13:00", "13:30"), ("14:30", "15:30"), ("16:00", "16:30")],
    "Tuesday": [("10:00", "10:30"), ("11:00", "12:00"), ("14:00", "16:00"), ("16:30", "17:00")],
}

jesse_busy = {
    "Monday": [("09:00", "17:00")],
    "Tuesday": [("11:00", "11:30"), ("12:00", "12:30"), ("13:00", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")],
}

days_in_order = ["Monday", "Tuesday"]

def find_slot():
    for day in days_in_order:
        ws, we = map(to_minutes, work_hours[day])
        p_busy = [(to_minutes(s), to_minutes(e)) for s, e in patricia_busy.get(day, [])]
        j_busy = [(to_minutes(s), to_minutes(e)) for s, e in jesse_busy.get(day, [])]

        p_free = clamp_and_free(ws, we, p_busy)
        j_free = clamp_and_free(ws, we, j_busy)

        common = intersect_intervals(p_free, j_free)
        for s, e in common:
            if e - s >= duration_min:
                start = s
                end = s + duration_min
                return day, start, end
    return None

result = find_slot()
if result:
    day, start, end = result
    print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")
else:
    print("No available slot found.")