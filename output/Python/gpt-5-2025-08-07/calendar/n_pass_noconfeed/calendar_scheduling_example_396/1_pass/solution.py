from typing import List, Tuple

def parse_time(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt_time(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def clamp_interval(interval: Tuple[int, int], bounds: Tuple[int, int]) -> Tuple[int, int]:
    start = max(interval[0], bounds[0])
    end = min(interval[1], bounds[1])
    return (start, end) if start < end else None

def invert_busy_to_free(busy: List[Tuple[int, int]], work_bounds: Tuple[int, int]) -> List[Tuple[int, int]]:
    # Normalize and clamp busy intervals within work bounds, then merge overlaps
    clamped = []
    for b in busy:
        c = clamp_interval(b, work_bounds)
        if c:
            clamped.append(c)
    clamped.sort()
    merged = []
    for s, e in clamped:
        if not merged or s > merged[-1][1]:
            merged.append([s, e])
        else:
            merged[-1][1] = max(merged[-1][1], e)
    merged = [(s, e) for s, e in merged]

    free = []
    cursor = work_bounds[0]
    for s, e in merged:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < work_bounds[1]:
        free.append((cursor, work_bounds[1]))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def find_meeting(common_free: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in common_free:
        if e - s >= duration:
            return (s, s + duration)
    return None

def main():
    day = "Monday"
    work_start, work_end = parse_time("09:00"), parse_time("17:00")
    work_bounds = (work_start, work_end)
    duration = 30  # minutes

    schedules = {
        "Andrea": [],
        "Jack": [("09:00","09:30"), ("14:00","14:30")],
        "Madison": [("09:30","10:30"), ("13:00","14:00"), ("15:00","15:30"), ("16:30","17:00")],
        "Rachel": [("09:30","10:30"), ("11:00","11:30"), ("12:00","13:30"), ("14:30","15:30"), ("16:00","17:00")],
        "Douglas": [("09:00","11:30"), ("12:00","16:30")],
        "Ryan": [("09:00","09:30"), ("13:00","14:00"), ("14:30","17:00")],
    }

    # Convert to minutes
    busy_minutes = {
        person: [(parse_time(s), parse_time(e)) for s, e in intervals]
        for person, intervals in schedules.items()
    }

    # Compute free intervals for each participant
    free_by_person = {
        person: invert_busy_to_free(intervals, work_bounds)
        for person, intervals in busy_minutes.items()
    }

    # Intersect all free intervals to get common availability
    participants = list(free_by_person.keys())
    common_free = free_by_person[participants[0]][:]
    for person in participants[1:]:
        common_free = intersect_intervals(common_free, free_by_person[person])

    meeting = find_meeting(common_free, duration)
    if not meeting:
        raise SystemExit("No suitable time found.")

    start_str, end_str = fmt_time(meeting[0]), fmt_time(meeting[1])

    # Output must include both the time range and the day of the week
    print(day)
    print(f"{{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()