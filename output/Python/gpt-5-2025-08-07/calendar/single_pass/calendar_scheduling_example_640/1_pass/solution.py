from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def from_minutes(m: int) -> str:
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

def invert_intervals(busy: List[Tuple[int, int]], day_start: int, day_end: int) -> List[Tuple[int, int]]:
    busy = merge_intervals([(max(day_start, s), min(day_end, e)) for s, e in busy if e > day_start and s < day_end])
    free = []
    cur = day_start
    for s, e in busy:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < day_end:
        free.append((cur, day_end))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    out = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            out.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return out

def intersect_all(lists: List[List[Tuple[int, int]]]) -> List[Tuple[int, int]]:
    if not lists:
        return []
    result = lists[0]
    for lst in lists[1:]:
        result = intersect_two(result, lst)
        if not result:
            break
    return result

# Input data
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
duration = 30  # minutes
days = ["Monday", "Tuesday"]

schedules = {
    "Bobby": {
        "Monday": [("14:30", "15:00")],
        "Tuesday": [("09:00", "11:30"), ("12:00", "12:30"), ("13:00", "15:00"), ("15:30", "17:00")],
    },
    "Michael": {
        "Monday": [("09:00", "10:00"), ("10:30", "13:30"), ("14:00", "15:00"), ("15:30", "17:00")],
        "Tuesday": [("09:00", "10:30"), ("11:00", "11:30"), ("12:00", "14:00"), ("15:00", "16:00"), ("16:30", "17:00")],
    },
}

# Convert to minutes
schedules_min = {
    person: {
        day: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
        for day, intervals in days_sched.items()
    }
    for person, days_sched in schedules.items()
}

proposed = None

for day in days:
    # Compute free intervals per participant for this day
    free_per_person = []
    for person in schedules_min:
        busy = schedules_min[person].get(day, [])
        free = invert_intervals(busy, work_start, work_end)
        free_per_person.append(free)
    # Common free intervals
    common = intersect_all(free_per_person)
    # Find earliest slot that fits the duration
    for s, e in common:
        if e - s >= duration:
            start = s
            end = s + duration
            proposed = (day, start, end)
            break
    if proposed:
        break

if proposed:
    day, start, end = proposed
    print(f"{day} {{{from_minutes(start)}:{from_minutes(end)}}}")
else:
    print("No available slot found.")