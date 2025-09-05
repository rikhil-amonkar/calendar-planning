from typing import List, Tuple, Dict

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def complement_within(intervals: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    intervals = merge_intervals([i for i in intervals if i[1] > start and i[0] < end])
    free = []
    cur = start
    for s, e in intervals:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    inter = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            inter.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return inter

def first_slot(intervals: List[Tuple[int, int]], duration: int) -> Tuple[int, int] or None:
    for s, e in intervals:
        if e - s >= duration:
            return (s, s + duration)
    return None

# Problem setup
work_start = to_minutes("09:00")
work_end   = to_minutes("17:00")
duration_minutes = 60

days = ["Monday", "Tuesday", "Wednesday"]

# Blocked schedules
martha_blocked: Dict[str, List[Tuple[int, int]]] = {
    "Monday":    [(to_minutes("16:00"), to_minutes("17:00"))],
    "Tuesday":   [(to_minutes("15:00"), to_minutes("15:30"))],
    "Wednesday": [(to_minutes("10:00"), to_minutes("11:00")),
                  (to_minutes("14:00"), to_minutes("14:30"))],
}

beverly_blocked: Dict[str, List[Tuple[int, int]]] = {
    "Monday":    [(to_minutes("09:00"), to_minutes("13:30")),
                  (to_minutes("14:00"), to_minutes("17:00"))],
    "Tuesday":   [(to_minutes("09:00"), to_minutes("17:00"))],
    "Wednesday": [(to_minutes("09:30"), to_minutes("15:30")),
                  (to_minutes("16:30"), to_minutes("17:00"))],
}

def find_meeting():
    for day in days:
        martha_free = complement_within(martha_blocked.get(day, []), work_start, work_end)
        beverly_free = complement_within(beverly_blocked.get(day, []), work_start, work_end)
        common = intersect_two(martha_free, beverly_free)
        slot = first_slot(common, duration_minutes)
        if slot:
            start_str = to_hhmm(slot[0])
            end_str = to_hhmm(slot[1])
            print(f"{day} {{{start_str}:{end_str}}}")
            return
    print("No available slot found")

if __name__ == "__main__":
    find_meeting()