from datetime import datetime

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals):
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

def clip_interval(interval, bounds):
    s, e = interval
    bs, be = bounds
    s = max(s, bs)
    e = min(e, be)
    return (s, e) if s < e else None

def invert_within(bounds, busy):
    bs, be = bounds
    busy = merge_intervals([iv for iv in (clip_interval(iv, bounds) for iv in busy) if iv])
    free = []
    cur = bs
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < be:
        free.append((cur, be))
    return free

def intersect_intervals(a, b):
    i, j = 0, 0
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

# Problem setup
day = "Monday"
work_bounds = (to_minutes("09:00"), to_minutes("17:00"))
duration = 30  # minutes

schedules = {
    "Bradley":   [("09:30","10:00"), ("12:30","13:00"), ("13:30","14:00"), ("15:30","16:00")],
    "Teresa":    [("10:30","11:00"), ("12:00","12:30"), ("13:00","13:30"), ("14:30","15:00")],
    "Elizabeth": [("09:00","09:30"), ("10:30","11:30"), ("13:00","13:30"), ("14:30","15:00"), ("15:30","17:00")],
    "Christian": [("09:00","09:30"), ("10:30","17:00")],
}

# Convert to minutes
busy_minutes = {
    person: [(to_minutes(s), to_minutes(e)) for s, e in times]
    for person, times in schedules.items()
}

# Compute free intervals per participant within work hours
free_by_person = {
    person: invert_within(work_bounds, times)
    for person, times in busy_minutes.items()
}

# Intersect all free intervals
common_free = None
for person, free in free_by_person.items():
    if common_free is None:
        common_free = free
    else:
        common_free = intersect_intervals(common_free, free)

# Find earliest slot meeting duration
meeting_start, meeting_end = None, None
for s, e in common_free or []:
    if e - s >= duration:
        meeting_start, meeting_end = s, s + duration
        break

if meeting_start is None:
    raise SystemExit("No suitable time found")

print(f"{{{to_hhmm(meeting_start)}:{to_hhmm(meeting_end)}}} {day}")