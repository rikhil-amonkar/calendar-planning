from typing import List, Tuple, Dict

# Utility functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time_str(m: int) -> str:
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

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
    start, end = window
    if not busy:
        return [(start, end)]
    busy = merge_intervals([(max(start, s), min(end, e)) for s, e in busy if min(end, e) > max(start, s)])
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

# Input data
days = ["Monday", "Tuesday", "Wednesday"]
work_window = (to_minutes("09:00"), to_minutes("17:00"))
meeting_duration = 30  # minutes
allowed_days = {"Monday", "Tuesday", "Wednesday"}

calendars: Dict[str, Dict[str, List[Tuple[int, int]]]] = {
    "Nicole": {
        "Monday":   [(to_minutes("09:00"), to_minutes("09:30")),
                     (to_minutes("13:00"), to_minutes("13:30")),
                     (to_minutes("14:30"), to_minutes("15:30"))],
        "Tuesday":  [(to_minutes("09:00"), to_minutes("09:30")),
                     (to_minutes("11:30"), to_minutes("13:30")),
                     (to_minutes("14:30"), to_minutes("15:30"))],
        "Wednesday":[(to_minutes("10:00"), to_minutes("11:00")),
                     (to_minutes("12:30"), to_minutes("15:00")),
                     (to_minutes("16:00"), to_minutes("17:00"))],
    },
    "Ruth": {
        "Monday":   [(to_minutes("09:00"), to_minutes("17:00"))],
        "Tuesday":  [(to_minutes("09:00"), to_minutes("17:00"))],
        "Wednesday":[(to_minutes("09:00"), to_minutes("10:30")),
                     (to_minutes("11:00"), to_minutes("11:30")),
                     (to_minutes("12:00"), to_minutes("12:30")),
                     (to_minutes("13:30"), to_minutes("15:30")),
                     (to_minutes("16:00"), to_minutes("16:30"))],
    }
}

# Additional constraint: Ruth does not want to meet on Wednesday after 13:30.
# Implement by adding a busy block from 13:30 to end of workday on Wednesday for Ruth.
ruth_cutoff = to_minutes("13:30")
calendars["Ruth"]["Wednesday"] = calendars["Ruth"]["Wednesday"] + [(ruth_cutoff, work_window[1])]

def find_meeting():
    participants = list(calendars.keys())
    for day in days:
        if day not in allowed_days:
            continue

        # Compute each participant's free slots within work window for the day
        free_lists = []
        for person in participants:
            busy = calendars[person].get(day, [])
            free = invert_intervals(busy, work_window)
            free_lists.append(free)

        # Intersect all participants' free slots
        common = free_lists[0]
        for lst in free_lists[1:]:
            common = intersect_intervals(common, lst)
            if not common:
                break

        # Find a slot with required duration
        for s, e in common:
            if e - s >= meeting_duration:
                start = s
                end = s + meeting_duration
                return day, start, end
    return None, None, None

day, start, end = find_meeting()

if day is None:
    print("No feasible meeting time found")
else:
    time_range = f"{to_time_str(start)}:{to_time_str(end)}"
    print(f"{day} {{{time_range}}}")