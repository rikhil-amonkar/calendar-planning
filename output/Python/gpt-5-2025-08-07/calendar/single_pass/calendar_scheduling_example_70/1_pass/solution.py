from functools import reduce

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
        last_s, last_e = merged[-1]
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def clip_interval(interval, window):
    s, e = interval
    ws, we = window
    if e <= ws or s >= we:
        return None
    return max(s, ws), min(e, we)

def invert_intervals(busy, window):
    ws, we = window
    busy = [clip for clip in (clip_interval(iv, window) for iv in busy) if clip]
    busy = merge_intervals(busy)
    free = []
    cur = ws
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < we:
        free.append((cur, we))
    return free

def intersect_two(a, b):
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

# Setup
day = "Monday"
work_window = (to_minutes("09:00"), to_minutes("17:00"))
duration = 30  # minutes

schedules_busy = {
    "Denise": [("12:00","12:30"), ("15:30","16:00")],
    "Angela": [],
    "Natalie": [("09:00","11:30"), ("12:00","13:00"), ("14:00","14:30"), ("15:00","17:00")],
}

# Convert to minutes
schedules_busy = {
    p: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    for p, intervals in schedules_busy.items()
}

# Compute each participant's free intervals within work window
free_by_person = [invert_intervals(schedules_busy[p], work_window) for p in schedules_busy]

# Intersection of all free intervals
common_free = reduce(intersect_two, free_by_person)

# Find earliest slot that fits the duration
start_time = end_time = None
for s, e in common_free:
    if e - s >= duration:
        start_time = s
        end_time = s + duration
        break

# Output
if start_time is not None:
    print(day)
    print(f"{{{to_hhmm(start_time)}:{to_hhmm(end_time)}}}")
else:
    # Fallback (should not occur per problem statement)
    print(day)
    print("{No available slot}")