# Meeting Scheduler for Monday between 09:00 and 17:00

from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:  # overlap or adjacent
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def clip_interval(interval: Tuple[int, int], window: Tuple[int, int]) -> Tuple[int, int] | None:
    s, e = interval
    ws, we = window
    s = max(s, ws)
    e = min(e, we)
    if s >= e:
        return None
    return (s, e)

def compute_free(busy: List[Tuple[str, str]], work_window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = work_window
    # Convert and clip busy intervals to the work window
    busy_minutes = []
    for s, e in busy:
        iv = clip_interval((to_minutes(s), to_minutes(e)), work_window)
        if iv:
            busy_minutes.append(iv)
    # Merge busy intervals
    busy_minutes = merge_intervals(busy_minutes)
    # Subtract from work window to get free intervals
    free = []
    prev_end = ws
    for s, e in busy_minutes:
        if s > prev_end:
            free.append((prev_end, s))
        prev_end = max(prev_end, e)
    if prev_end < we:
        free.append((prev_end, we))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i, j = 0, 0
    result = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            result.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return result

def find_slot(intersections: List[Tuple[int, int]], duration: int) -> Tuple[int, int] | None:
    for s, e in intersections:
        if e - s >= duration:
            return (s, s + duration)
    return None

def main():
    day = "Monday"
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    duration = 30  # minutes

    schedules = {
        "Diane":     [("09:30", "10:00"), ("14:30", "15:00")],
        "Jack":      [("13:30", "14:00"), ("14:30", "15:00")],
        "Eugene":    [("09:00", "10:00"), ("10:30", "11:30"), ("12:00", "14:30"), ("15:00", "16:30")],
        "Patricia":  [("09:30", "10:30"), ("11:00", "12:00"), ("12:30", "14:00"), ("15:00", "16:30")],
    }

    work_window = (work_start, work_end)

    # Compute free intervals for each participant
    free_lists = []
    for participant, busy in schedules.items():
        free_lists.append(compute_free(busy, work_window))

    # Intersect free intervals across all participants
    from functools import reduce
    common_free = reduce(intersect_intervals, free_lists)

    # Find earliest suitable slot of required duration
    slot = find_slot(common_free, duration)
    if not slot:
        raise RuntimeError("No suitable slot found, but the problem statement guarantees one exists.")

    start_str, end_str = to_hhmm(slot[0]), to_hhmm(slot[1])

    # Output: Day and time range in {HH:MM:HH:MM}
    print(day)
    print(f"{{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()