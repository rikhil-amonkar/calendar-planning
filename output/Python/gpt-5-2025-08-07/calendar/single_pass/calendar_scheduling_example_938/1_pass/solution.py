from typing import List, Tuple, Dict

# Time utilities
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def invert_within(intervals: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    free = []
    cur = start
    for s, e in merge_intervals([iv for iv in intervals if iv[1] > start and iv[0] < end]):
        s, e = max(s, start), min(e, end)
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

# Parameters
WORK_START = to_minutes("09:00")
WORK_END = to_minutes("17:00")
DURATION = 30  # minutes
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Preference: Eric would like to avoid more meetings on Wednesday (deprioritize Wednesday)
day_priority = ["Monday", "Tuesday", "Thursday", "Friday", "Wednesday"]

# Schedules (busy times)
eugene_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday":   [(to_minutes("11:00"), to_minutes("12:00")),
                 (to_minutes("13:30"), to_minutes("14:00")),
                 (to_minutes("14:30"), to_minutes("15:00")),
                 (to_minutes("16:00"), to_minutes("16:30"))],
    "Tuesday":  [],
    "Wednesday":[(to_minutes("09:00"), to_minutes("09:30")),
                 (to_minutes("11:00"), to_minutes("11:30")),
                 (to_minutes("12:00"), to_minutes("12:30")),
                 (to_minutes("13:30"), to_minutes("15:00"))],
    "Thursday": [(to_minutes("09:30"), to_minutes("10:00")),
                 (to_minutes("11:00"), to_minutes("12:30"))],
    "Friday":   [(to_minutes("10:30"), to_minutes("11:00")),
                 (to_minutes("12:00"), to_minutes("12:30")),
                 (to_minutes("13:00"), to_minutes("13:30"))],
}

eric_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday":   [(to_minutes("09:00"), to_minutes("17:00"))],
    "Tuesday":  [(to_minutes("09:00"), to_minutes("17:00"))],
    "Wednesday":[(to_minutes("09:00"), to_minutes("11:30")),
                 (to_minutes("12:00"), to_minutes("14:00")),
                 (to_minutes("14:30"), to_minutes("16:30"))],
    "Thursday": [(to_minutes("09:00"), to_minutes("17:00"))],
    "Friday":   [(to_minutes("09:00"), to_minutes("11:00")),
                 (to_minutes("11:30"), to_minutes("17:00"))],
}

def find_slot() -> Tuple[str, str, str]:
    for day in day_priority:
        eug_free = invert_within(eugene_busy.get(day, []), WORK_START, WORK_END)
        eri_free = invert_within(eric_busy.get(day, []), WORK_START, WORK_END)
        common = intersect(eug_free, eri_free)
        for s, e in common:
            if e - s >= DURATION:
                start = s
                end = s + DURATION
                return day, fmt(start), fmt(end)
    raise ValueError("No suitable time found")

if __name__ == "__main__":
    day, start_str, end_str = find_slot()
    print(day)
    print(f"{{{start_str}:{end_str}}}")