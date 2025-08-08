from typing import List, Tuple

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_timestr(m: int) -> str:
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

def invert_intervals(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
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

# Data
DAYS = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
WORK_START = to_minutes("09:00")
WORK_END = to_minutes("17:00")
DURATION = 60  # minutes

busy = {
    "Nicole": {
        "Monday": [],
        "Tuesday": [("16:00", "16:30")],
        "Wednesday": [("15:00", "15:30")],
        "Thursday": [],
        "Friday": [("12:00", "12:30"), ("15:30", "16:00")],
    },
    "Daniel": {
        "Monday": [("09:00", "12:30"), ("13:00", "13:30"), ("14:00", "16:30")],
        "Tuesday": [("09:00", "10:30"), ("11:30", "12:30"), ("13:00", "13:30"), ("15:00", "16:00"), ("16:30", "17:00")],
        "Wednesday": [("09:00", "10:00"), ("11:00", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("16:30", "17:00")],
        "Thursday": [("11:00", "12:00"), ("13:00", "14:00"), ("15:00", "15:30")],
        "Friday": [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "14:30"), ("15:00", "15:30"), ("16:00", "16:30")],
    },
}

# Convert busy times to minutes and merge per day
busy_minutes = {}
for person, days in busy.items():
    busy_minutes[person] = {}
    for day in DAYS:
        intervals = [(to_minutes(s), to_minutes(e)) for s, e in days.get(day, [])]
        # Clamp to work hours and drop anything outside
        clamped = []
        for s, e in intervals:
            s = max(s, WORK_START)
            e = min(e, WORK_END)
            if s < e:
                clamped.append((s, e))
        busy_minutes[person][day] = merge_intervals(clamped)

# Find earliest common availability
for day in DAYS:
    # Free intervals per person
    nic_free = invert_intervals(busy_minutes["Nicole"][day], WORK_START, WORK_END)
    dan_free = invert_intervals(busy_minutes["Daniel"][day], WORK_START, WORK_END)
    # Intersect
    common = intersect_intervals(nic_free, dan_free)
    # Look for earliest slot of required duration
    for s, e in common:
        if e - s >= DURATION:
            start = s
            end = s + DURATION
            print(f"{day} {{{to_timestr(start)}:{to_timestr(end)}}}")
            raise SystemExit

# If somehow not found (though problem states a solution exists)
print("No available slot found")