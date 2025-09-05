# Meeting scheduler for the given participants and constraints.
# Outputs the day of the week and a proposed meeting time range in the format {HH:MM:HH:MM}.

from typing import List, Tuple

Day = "Monday"
WORK_START = "09:00"
WORK_END = "17:00"
MEETING_DURATION_MIN = 30  # minutes

busy_schedules = {
    "Joe": [
        ("09:30", "10:00"),
        ("10:30", "11:00"),
    ],
    "Keith": [
        ("11:30", "12:00"),
        ("15:00", "15:30"),
    ],
    "Patricia": [
        ("09:00", "09:30"),
        ("13:00", "13:30"),
    ],
    "Nancy": [
        ("09:00", "11:00"),
        ("11:30", "16:30"),
    ],
    "Pamela": [
        ("09:00", "10:00"),
        ("10:30", "11:00"),
        ("11:30", "12:30"),
        ("13:00", "14:00"),
        ("14:30", "15:00"),
        ("15:30", "16:00"),
        ("16:30", "17:00"),
    ],
}

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

def clamp_intervals(intervals: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    clamped = []
    for s, e in intervals:
        cs, ce = max(s, start), min(e, end)
        if cs < ce:
            clamped.append((cs, ce))
    return clamped

def invert_intervals(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    if not busy:
        return [(start, end)]
    free = []
    cursor = start
    for s, e in busy:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < end:
        free.append((cursor, end))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    result = []
    while i < len(a) and j < len(b):
        s1, e1 = a[i]
        s2, e2 = b[j]
        s, e = max(s1, s2), min(e1, e2)
        if s < e:
            result.append((s, e))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return result

def intersect_all(lists: List[List[Tuple[int, int]]]) -> List[Tuple[int, int]]:
    if not lists:
        return []
    inter = lists[0]
    for other in lists[1:]:
        inter = intersect_two(inter, other)
        if not inter:
            break
    return inter

def find_meeting():
    ws, we = to_minutes(WORK_START), to_minutes(WORK_END)
    participants_free = []
    for person, blocks in busy_schedules.items():
        busy_min = [(to_minutes(s), to_minutes(e)) for s, e in blocks]
        busy_min = clamp_intervals(merge_intervals(busy_min), ws, we)
        free_min = invert_intervals(busy_min, ws, we)
        participants_free.append(free_min)

    common_free = intersect_all(participants_free)
    # Find the earliest slot that can fit the meeting duration
    for s, e in common_free:
        if e - s >= MEETING_DURATION_MIN:
            start = s
            end = s + MEETING_DURATION_MIN
            print(Day)
            print(f"{{{to_hhmm(start)}:{to_hhmm(end)}}}")
            return

    # By problem statement, a solution exists; this is a safeguard.
    raise RuntimeError("No common slot found, but a solution was expected.")

if __name__ == "__main__":
    find_meeting()