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

def complement_intervals(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    busy = merge_intervals([(max(start, s), min(end, e)) for s, e in busy if e > start and s < end])
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

def intersect(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    duration = 30  # minutes

    busy_str = {
        "Daniel": [],
        "Kathleen": [("14:30", "15:30")],
        "Carolyn": [("12:00", "12:30"), ("13:00", "13:30")],
        "Roger": [],  # Preference handled below (not before 12:30)
        "Cheryl": [("09:00", "09:30"), ("10:00", "11:30"), ("12:30", "13:30"), ("14:00", "17:00")],
        "Virginia": [("09:30", "11:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "15:30"), ("16:00", "17:00")],
        "Angela": [("09:30", "10:00"), ("10:30", "11:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:00", "16:30")],
    }

    # Convert to minutes
    busy = {p: [(to_minutes(s), to_minutes(e)) for s, e in intervals] for p, intervals in busy_str.items()}

    # Roger's preference: not before 12:30 on Monday
    roger_not_before = to_minutes("12:30")
    busy["Roger"] = merge_intervals(busy["Roger"] + [(work_start, roger_not_before)])

    # Compute each participant's free intervals within work hours
    free_by_person = {
        p: complement_intervals(intervals, work_start, work_end)
        for p, intervals in busy.items()
    }

    # Intersect all free intervals
    participants = list(free_by_person.keys())
    common_free = free_by_person[participants[0]][:]
    for p in participants[1:]:
        common_free = intersect(common_free, free_by_person[p])
        if not common_free:
            break

    # Choose the earliest slot of required duration
    for s, e in common_free:
        if e - s >= duration:
            start_str, end_str = to_hhmm(s), to_hhmm(s + duration)
            print(day)
            print(f"{{{start_str}:{end_str}}}")
            return

    raise RuntimeError("No suitable time found, but a solution was expected.")

if __name__ == "__main__":
    find_meeting()