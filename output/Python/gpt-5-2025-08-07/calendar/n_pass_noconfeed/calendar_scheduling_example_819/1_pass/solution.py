from typing import List, Tuple

# Time helpers
def t2m(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def m2t(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

Interval = Tuple[int, int]

def merge_intervals(intervals: List[Interval]) -> List[Interval]:
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for start, end in intervals[1:]:
        last_start, last_end = merged[-1]
        if start <= last_end:
            merged[-1] = (last_start, max(last_end, end))
        else:
            merged.append((start, end))
    return merged

def subtract_from_base(base: Interval, blocks: List[Interval]) -> List[Interval]:
    # Subtract blocks from base interval, returning list of remaining intervals
    blocks = merge_intervals([b for b in blocks if not (b[1] <= base[0] or b[0] >= base[1])])
    free = []
    cur = base[0]
    for b_start, b_end in blocks:
        if b_start > cur:
            free.append((cur, b_start))
        cur = max(cur, b_end)
        if cur >= base[1]:
            break
    if cur < base[1]:
        free.append((cur, base[1]))
    return free

def intersect_two(a: List[Interval], b: List[Interval]) -> List[Interval]:
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

def find_first_slot(intervals: List[Interval], duration: int) -> Interval or None:
    for s, e in intervals:
        if e - s >= duration:
            return (s, s + duration)
    return None

# Problem setup
work_start = t2m("09:00")
work_end = t2m("17:00")
work_window = (work_start, work_end)
meeting_duration = 30

days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Participants' busy schedules
# Julie has no meetings the whole week.
julie_busy = {day: [] for day in days}

# Preference: Julie would like to avoid more meetings on Thursday before 11:30.
# Treat as a constraint since a valid slot exists later.
julie_busy["Thursday"].append((t2m("09:00"), t2m("11:30")))

# Ruth's schedule
ruth_busy = {
    "Monday":   [(t2m("09:00"), t2m("17:00"))],
    "Tuesday":  [(t2m("09:00"), t2m("17:00"))],
    "Wednesday":[(t2m("09:00"), t2m("17:00"))],
    "Thursday": [
        (t2m("09:00"), t2m("11:00")),
        (t2m("11:30"), t2m("14:30")),
        (t2m("15:00"), t2m("17:00")),
    ],
}

participants = [
    ("Julie", julie_busy),
    ("Ruth", ruth_busy),
]

# Search for the earliest valid slot in order of days
for day in days:
    # Compute each participant's free intervals within work hours
    free_lists = []
    for _, sched in participants:
        busy_today = merge_intervals(sched.get(day, []))
        free_today = subtract_from_base(work_window, busy_today)
        free_lists.append(free_today)

    # Intersect all participants' free intervals
    common_free = free_lists[0]
    for fl in free_lists[1:]:
        common_free = intersect_two(common_free, fl)
        if not common_free:
            break

    # Find the first slot of required duration
    slot = find_first_slot(common_free, meeting_duration)
    if slot:
        start, end = slot
        print(f"{m2t(start)}:{m2t(end)}")
        print(day)
        break