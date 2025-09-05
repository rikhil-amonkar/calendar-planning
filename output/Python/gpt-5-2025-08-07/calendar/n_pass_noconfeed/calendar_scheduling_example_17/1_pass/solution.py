from typing import List, Tuple

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
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def complement_within(bounds: Tuple[int, int], blocks: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    start, end = bounds
    if not blocks:
        return [(start, end)]
    blocks = merge_intervals([(max(start, s), min(end, e)) for s, e in blocks if e > start and s < end])
    free = []
    cur = start
    for s, e in blocks:
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

def cut_by_latest_end(intervals: List[Tuple[int, int]], latest_end: int) -> List[Tuple[int, int]]:
    cut = []
    for s, e in intervals:
        ne = min(e, latest_end)
        if s < ne:
            cut.append((s, ne))
    return cut

# Problem setup
day = "Monday"
work_start, work_end = "09:00", "17:00"
meeting_duration_min = 30

work_bounds = (to_minutes(work_start), to_minutes(work_end))

# Blocked schedules (inclusive of meeting times) on Monday
margaret_blocks = [
    ("09:00","10:00"), ("10:30","11:00"), ("11:30","12:00"),
    ("13:00","13:30"), ("15:00","15:30")
]
donna_blocks = [
    ("14:30","15:00"), ("16:00","16:30")
]
helen_blocks = [
    ("09:00","09:30"), ("10:00","11:30"), ("13:00","14:00"),
    ("14:30","15:00"), ("15:30","17:00")
]

# Convert to minutes
margaret_blocks_min = [(to_minutes(s), to_minutes(e)) for s, e in margaret_blocks]
donna_blocks_min = [(to_minutes(s), to_minutes(e)) for s, e in donna_blocks]
helen_blocks_min = [(to_minutes(s), to_minutes(e)) for s, e in helen_blocks]

# Free intervals within work bounds
margaret_free = complement_within(work_bounds, margaret_blocks_min)
donna_free = complement_within(work_bounds, donna_blocks_min)
helen_free = complement_within(work_bounds, helen_blocks_min)

# Intersect all participants' free times
group_free = intersect(intersect(margaret_free, donna_free), helen_free)

# Helen preference: not after 13:30 (meeting must end no later than 13:30)
latest_end_pref = to_minutes("13:30")
group_free = cut_by_latest_end(group_free, latest_end_pref)

# Find earliest slot of required duration
proposed = None
for s, e in group_free:
    if e - s >= meeting_duration_min:
        proposed = (s, s + meeting_duration_min)
        break

# Output the result
if proposed:
    start_str = to_hhmm(proposed[0])
    end_str = to_hhmm(proposed[1])
    print(f"{start_str}:{end_str}")
    print(day)
else:
    # According to the problem statement a solution exists, but handle gracefully just in case
    print("No available time slot found")
    print(day)