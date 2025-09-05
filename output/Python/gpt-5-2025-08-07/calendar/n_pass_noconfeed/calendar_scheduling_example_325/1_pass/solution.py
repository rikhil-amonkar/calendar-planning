from typing import List, Tuple

def time_to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:  # overlap or touching
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def clamp_intervals(intervals: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    clamped = []
    for s, e in intervals:
        s2 = max(s, start)
        e2 = min(e, end)
        if s2 < e2:
            clamped.append((s2, e2))
    return merge_intervals(clamped)

def invert_intervals(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    if not busy:
        return [(start, end)]
    free = []
    cur = start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
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

def find_slot(common_free: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in common_free:
        if e - s >= duration:
            return (s, s + duration)
    return (-1, -1)

def main():
    day = "Monday"
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    duration = 30  # minutes

    schedules = {
        "Jose": [("11:00", "11:30"), ("12:30", "13:00")],
        "Keith": [("14:00", "14:30"), ("15:00", "15:30")],
        "Logan": [("09:00", "10:00"), ("12:00", "12:30"), ("15:00", "15:30")],
        "Megan": [("09:00", "10:30"), ("11:00", "12:00"), ("13:00", "13:30"), ("14:30", "16:30")],
        "Gary": [("09:00", "09:30"), ("10:00", "10:30"), ("11:30", "13:00"), ("13:30", "14:00"), ("14:30", "16:30")],
        "Bobby": [("11:00", "11:30"), ("12:00", "12:30"), ("13:00", "16:00")],
    }

    # Apply Jose's preference: does not want to meet after 15:30 on Monday
    jose_latest_end = time_to_minutes("15:30")
    schedules["Jose"].append(("15:30", "17:00"))

    # Convert schedules to minute intervals and clamp to work hours
    busy_minutes = {}
    for person, blocks in schedules.items():
        mins = [(time_to_minutes(s), time_to_minutes(e)) for s, e in blocks]
        mins = clamp_intervals(mins, work_start, work_end)
        busy_minutes[person] = merge_intervals(mins)

    # Compute free intervals per person
    free_minutes = {}
    for person, busy in busy_minutes.items():
        free_minutes[person] = invert_intervals(busy, work_start, work_end)

    # Intersect free intervals across all participants
    participants = list(free_minutes.keys())
    common_free = free_minutes[participants[0]]
    for p in participants[1:]:
        common_free = intersect_intervals(common_free, free_minutes[p])

    # Find earliest slot of required duration
    start, end = find_slot(common_free, duration)

    if start == -1:
        raise SystemExit("No feasible slot found")

    start_str = minutes_to_time(start)
    end_str = minutes_to_time(end)
    print(f"{day} {{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()