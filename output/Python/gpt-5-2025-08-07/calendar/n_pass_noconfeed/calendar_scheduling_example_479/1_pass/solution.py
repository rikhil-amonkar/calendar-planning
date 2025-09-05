# Meeting scheduler for the given participants and constraints

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

def subtract_from_workday(busy, work_start, work_end):
    busy = merge_intervals([(max(work_start, s), min(work_end, e)) for s, e in busy if e > work_start and s < work_end])
    free = []
    cur = work_start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < work_end:
        free.append((cur, work_end))
    return free

def intersect_intervals(a, b):
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
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 60  # minutes

participants_busy = {
    "Evelyn": [],
    "Joshua": [("11:00","12:30"), ("13:30","14:30"), ("16:30","17:00")],
    "Kevin": [],
    "Gerald": [],
    "Jerry": [("09:00","09:30"), ("10:30","12:00"), ("12:30","13:00"), ("13:30","14:00"), ("14:30","15:00"), ("15:30","16:00")],
    "Jesse": [("09:00","09:30"), ("10:30","12:00"), ("12:30","13:00"), ("14:30","15:00"), ("15:30","16:30")],
    "Kenneth": [("10:30","12:30"), ("13:30","14:00"), ("14:30","15:00"), ("15:30","16:00"), ("16:30","17:00")],
}

# Convert to minutes
participants_busy_minutes = {
    p: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    for p, intervals in participants_busy.items()
}

# Compute free intervals per participant
participants_free = {
    p: subtract_from_workday(busy, work_start, work_end)
    for p, busy in participants_busy_minutes.items()
}

# Find common free intervals
common_free = [(work_start, work_end)]
for p, free in participants_free.items():
    common_free = intersect_intervals(common_free, free)
    if not common_free:
        break

# Select earliest slot of required duration
meeting_start = meeting_end = None
for s, e in common_free:
    if e - s >= duration:
        meeting_start = s
        meeting_end = s + duration
        break

if meeting_start is None:
    raise RuntimeError("No suitable meeting slot found, but the problem statement guarantees one exists.")

# Output
print(day)
print("{" + f"{to_hhmm(meeting_start)}:{to_hhmm(meeting_end)}" + "}")