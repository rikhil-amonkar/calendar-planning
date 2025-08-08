from typing import List, Tuple, Dict

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
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def invert_intervals(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
    free = []
    cur = ws
    for s, e in busy:
        if e <= cur:
            continue
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
        if cur >= we:
            break
    if cur < we:
        free.append((cur, we))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def intersect_all(lists: List[List[Tuple[int, int]]]) -> List[Tuple[int, int]]:
    if not lists:
        return []
    res = lists[0]
    for other in lists[1:]:
        res = intersect_two(res, other)
        if not res:
            break
    return res

# Input data
days = ["Monday", "Tuesday", "Wednesday"]
work_window = (to_minutes("09:00"), to_minutes("17:00"))
duration = 30  # minutes

schedules: Dict[str, Dict[str, List[Tuple[str, str]]]] = {
    "Nancy": {
        "Monday": [("10:00", "10:30"), ("11:30", "12:30"), ("13:30", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")],
        "Tuesday": [("09:30", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("15:30", "16:00")],
        "Wednesday": [("10:00", "11:30"), ("13:30", "16:00")],
    },
    "Jose": {
        "Monday": [("09:00", "17:00")],
        "Tuesday": [("09:00", "17:00")],
        "Wednesday": [("09:00", "09:30"), ("10:00", "12:30"), ("13:30", "14:30"), ("15:00", "17:00")],
    }
}

# Compute earliest slot
for day in days:
    participants_free: List[List[Tuple[int, int]]] = []
    for person, cal in schedules.items():
        busy_minutes = merge_intervals([(to_minutes(s), to_minutes(e)) for s, e in cal.get(day, [])])
        free_minutes = invert_intervals(busy_minutes, work_window)
        participants_free.append(free_minutes)

    common = intersect_all(participants_free)
    # Find earliest interval with enough duration
    for s, e in common:
        if e - s >= duration:
            start = s
            end = s + duration
            print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")
            raise SystemExit

# If somehow not found (though the prompt guarantees a solution)
print("No available slot found")