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
    for start, end in intervals[1:]:
        last_start, last_end = merged[-1]
        if start <= last_end:
            merged[-1] = (last_start, max(last_end, end))
        else:
            merged.append((start, end))
    return merged

def invert_intervals(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
    if not busy:
        return [(ws, we)]
    free = []
    prev_end = ws
    for s, e in busy:
        s = max(s, ws)
        e = min(e, we)
        if s > prev_end:
            free.append((prev_end, s))
        prev_end = max(prev_end, e)
    if prev_end < we:
        free.append((prev_end, we))
    return free

def find_earliest_slot(free_intervals: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in free_intervals:
        if e - s >= duration:
            return (s, s + duration)
    return (-1, -1)

def main():
    day = "Monday"
    work_start, work_end = "09:00", "17:00"
    duration_min = 30

    # Participants' busy schedules for Monday
    andrews_busy = []  # Andrew's calendar is wide open
    graces_busy = []   # Grace has no meetings
    samuels_busy = [
        ("09:00", "10:30"),
        ("11:30", "12:00"),
        ("13:00", "13:30"),
        ("14:00", "16:00"),
        ("16:30", "17:00"),
    ]

    # Convert to minutes
    work_window = (to_minutes(work_start), to_minutes(work_end))
    all_busy = []
    for cal in (andrews_busy, graces_busy, samuels_busy):
        for s, e in cal:
            all_busy.append((to_minutes(s), to_minutes(e)))

    # Keep only busy intervals that intersect the work window
    ws, we = work_window
    all_busy = [(max(s, ws), min(e, we)) for s, e in all_busy if min(e, we) > max(s, ws)]

    # Merge busy intervals across participants
    merged_busy = merge_intervals(all_busy)

    # Compute free intervals within work window
    free_intervals = invert_intervals(merged_busy, work_window)

    # Find earliest slot fitting the duration
    start, end = find_earliest_slot(free_intervals, duration_min)

    # Output in required format: {HH:MM:HH:MM} Day
    print(f"{{{to_hhmm(start)}:{to_hhmm(end)}}} {day}")

if __name__ == "__main__":
    main()