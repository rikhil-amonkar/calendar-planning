from typing import List, Tuple, Dict

def minutes(h: int, m: int) -> int:
    return h * 60 + m

def fmt(t: int) -> str:
    return f"{t // 60:02d}:{t % 60:02d}"

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

def invert_busy(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    busy = merge_intervals([(max(work_start, s), min(work_end, e)) for s, e in busy if e > work_start and s < work_end])
    free = []
    cursor = work_start
    for s, e in busy:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < work_end:
        free.append((cursor, work_end))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

# Configuration
work_start = minutes(9, 0)
work_end = minutes(17, 0)
duration = 60  # one hour
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

schedules: Dict[str, Dict[str, List[Tuple[int, int]]]] = {
    "Natalie": {
        "Monday":   [(minutes(9,0), minutes(9,30)), (minutes(10,0), minutes(12,0)), (minutes(12,30), minutes(13,0)),
                     (minutes(14,0), minutes(14,30)), (minutes(15,0), minutes(16,30))],
        "Tuesday":  [(minutes(9,0), minutes(9,30)), (minutes(10,0), minutes(10,30)), (minutes(12,30), minutes(14,0)),
                     (minutes(16,0), minutes(17,0))],
        "Wednesday":[(minutes(11,0), minutes(11,30)), (minutes(16,0), minutes(16,30))],
        "Thursday": [(minutes(10,0), minutes(11,0)), (minutes(11,30), minutes(15,0)), (minutes(15,30), minutes(16,0)),
                     (minutes(16,30), minutes(17,0))],
    },
    "William": {
        "Monday":   [(minutes(9,30), minutes(11,0)), (minutes(11,30), minutes(17,0))],
        "Tuesday":  [(minutes(9,0), minutes(13,0)), (minutes(13,30), minutes(16,0))],
        "Wednesday":[(minutes(9,0), minutes(12,30)), (minutes(13,0), minutes(14,30)), (minutes(15,30), minutes(16,0)),
                     (minutes(16,30), minutes(17,0))],
        "Thursday": [(minutes(9,0), minutes(10,30)), (minutes(11,0), minutes(11,30)), (minutes(12,0), minutes(12,30)),
                     (minutes(13,0), minutes(14,0)), (minutes(15,0), minutes(17,0))],
    }
}

def find_meeting():
    participants = list(schedules.keys())
    for day in days:
        # Compute free intervals for each participant
        free_by_person = []
        for person in participants:
            busy = schedules[person].get(day, [])
            free = invert_busy(busy, work_start, work_end)
            free_by_person.append(free)

        # Intersect all participants' free intervals
        common = free_by_person[0]
        for idx in range(1, len(free_by_person)):
            common = intersect_intervals(common, free_by_person[idx])
            if not common:
                break

        # Find earliest slot meeting the duration
        for s, e in common:
            if e - s >= duration:
                start = s
                end = s + duration
                print(day)
                print(f"{fmt(start)}:{fmt(end)}")
                return

find_meeting()