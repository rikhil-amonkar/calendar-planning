from typing import List, Tuple

def parse_time(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def format_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

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

def clip_intervals(intervals: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
    clipped = []
    for s, e in intervals:
        cs, ce = max(ws, s), min(we, e)
        if cs < ce:
            clipped.append((cs, ce))
    return clipped

def complement_within_window(blocked: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
    if not blocked:
        return [(ws, we)]
    blocked = merge_intervals(clip_intervals(blocked, window))
    free = []
    curr = ws
    for s, e in blocked:
        if curr < s:
            free.append((curr, s))
        curr = max(curr, e)
    if curr < we:
        free.append((curr, we))
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

def find_meeting(frees: List[List[Tuple[int, int]]], duration: int) -> Tuple[int, int]:
    # Intersect all participants' free intervals
    common = frees[0]
    for free in frees[1:]:
        common = intersect_intervals(common, free)
        if not common:
            return (-1, -1)
    # Find earliest slot of required duration
    for s, e in common:
        if e - s >= duration:
            return (s, s + duration)
    return (-1, -1)

def main():
    day = "Monday"
    work_start, work_end = parse_time("09:00"), parse_time("17:00")
    work_window = (work_start, work_end)
    meeting_duration = 60  # minutes

    # Existing schedules (blocked times)
    kayla_blocked_str = [("10:00", "10:30"), ("14:30", "16:00")]
    rebecca_blocked_str = [("09:00", "13:00"), ("13:30", "15:00"), ("15:30", "16:00")]

    kayla_blocked = [(parse_time(s), parse_time(e)) for s, e in kayla_blocked_str]
    rebecca_blocked = [(parse_time(s), parse_time(e)) for s, e in rebecca_blocked_str]

    # Compute free intervals within work window
    kayla_free = complement_within_window(kayla_blocked, work_window)
    rebecca_free = complement_within_window(rebecca_blocked, work_window)

    # Find a common meeting time
    start, end = find_meeting([kayla_free, rebecca_free], meeting_duration)

    if start == -1:
        raise ValueError("No available meeting time found with given constraints.")
    
    time_range = f"{format_time(start)}:{format_time(end)}"
    print(day)
    print(f"{{{time_range}}}")

if __name__ == "__main__":
    main()