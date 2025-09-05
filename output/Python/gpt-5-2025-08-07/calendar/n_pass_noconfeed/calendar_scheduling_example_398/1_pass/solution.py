from typing import List, Tuple

def parse_time(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def format_time(minutes: int) -> str:
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

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

def invert_intervals(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    if not busy:
        return [(work_start, work_end)]
    free = []
    current = work_start
    for s, e in busy:
        if current < s:
            free.append((current, s))
        current = max(current, e)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
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

def find_meeting_slot(common_free: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in common_free:
        if e - s >= duration:
            return (s, s + duration)
    raise ValueError("No suitable slot found")

def main():
    day = "Monday"
    work_start, work_end = parse_time("09:00"), parse_time("17:00")
    duration = 30  # minutes

    schedules = {
        "Doris":     [("09:00", "11:00"), ("13:30", "14:00"), ("16:00", "16:30")],
        "Theresa":   [("10:00", "12:00")],
        "Christian": [],
        "Terry":     [("09:30", "10:00"), ("11:30", "12:00"), ("12:30", "13:00"),
                      ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")],
        "Carolyn":   [("09:00", "10:30"), ("11:00", "11:30"), ("12:00", "13:00"),
                      ("13:30", "14:30"), ("15:00", "17:00")],
        "Kyle":      [("09:00", "09:30"), ("11:30", "12:00"), ("12:30", "13:00"),
                      ("14:30", "17:00")],
    }

    # Convert schedules to minutes and merge overlaps
    busy_minutes = {
        person: merge_intervals([(parse_time(s), parse_time(e)) for s, e in intervals])
        for person, intervals in schedules.items()
    }

    # Compute free intervals within work hours for each person
    free_minutes = {
        person: invert_intervals(busy, work_start, work_end)
        for person, busy in busy_minutes.items()
    }

    # Intersect all free intervals
    participants = list(free_minutes.keys())
    common_free = free_minutes[participants[0]][:]
    for person in participants[1:]:
        common_free = intersect_two(common_free, free_minutes[person])

    # Find the earliest slot that fits the duration
    start, end = find_meeting_slot(common_free, duration)

    # Output: include both the time range and the day of the week
    time_range = f"{format_time(start)}:{format_time(end)}"
    print(f"{day} {{{time_range}}}")

if __name__ == "__main__":
    main()