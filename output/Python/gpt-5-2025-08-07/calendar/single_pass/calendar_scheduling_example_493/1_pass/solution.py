from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_str(mins: int) -> str:
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

Interval = Tuple[int, int]

def normalize(intervals: List[Interval]) -> List[Interval]:
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

def subtract(base: List[Interval], blocks: List[Interval]) -> List[Interval]:
    # Subtract blocks from base intervals
    result = []
    blocks = normalize(blocks)
    for bs, be in base:
        curr = [(bs, be)]
        for cs, ce in blocks:
            new_curr = []
            for s, e in curr:
                if ce <= s or cs >= e:
                    # no overlap
                    new_curr.append((s, e))
                else:
                    # overlap; split as needed
                    if s < cs:
                        new_curr.append((s, cs))
                    if ce < e:
                        new_curr.append((ce, e))
            curr = new_curr
        result.extend(curr)
    return normalize(result)

def intersect(a: List[Interval], b: List[Interval]) -> List[Interval]:
    i, j = 0, 0
    res = []
    a = normalize(a)
    b = normalize(b)
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

# Meeting configuration
day = "Monday"
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
work_window = [(work_start, work_end)]
duration = 30  # minutes

# Participants' busy schedules (Monday)
schedules_busy = {
    "Tyler": [],
    "Kelly": [],
    "Stephanie": [("11:00","11:30"), ("14:30","15:00")],
    "Hannah": [],
    "Joe": [("09:00","09:30"), ("10:00","12:00"), ("12:30","13:00"), ("14:00","17:00")],
    "Diana": [("09:00","10:30"), ("11:30","12:00"), ("13:00","14:00"), ("14:30","15:30"), ("16:00","17:00")],
    "Deborah": [("09:00","10:00"), ("10:30","12:00"), ("12:30","13:00"), ("13:30","14:00"), ("14:30","15:30"), ("16:00","16:30")],
}

# Convert busy schedules to minutes and clip to work window
def clip_to_work(intervals: List[Tuple[str, str]]) -> List[Interval]:
    res = []
    for s, e in intervals:
        ms, me = to_minutes(s), to_minutes(e)
        if me <= work_start or ms >= work_end:
            continue
        res.append((max(ms, work_start), min(me, work_end)))
    return normalize(res)

# Compute common free time
common_free = work_window[:]
for person, busy in schedules_busy.items():
    busy_minutes = clip_to_work(busy)
    free_minutes = subtract(work_window, busy_minutes)
    common_free = intersect(common_free, free_minutes)

# Find earliest slot of required duration
start_time = end_time = None
for s, e in common_free:
    if e - s >= duration:
        start_time = s
        end_time = s + duration
        break

if start_time is None:
    raise RuntimeError("No available slot found, but problem statement guarantees a solution.")

time_range = f"{to_str(start_time)}:{to_str(end_time)}"
print(f"{{{time_range}}}")
print(day)