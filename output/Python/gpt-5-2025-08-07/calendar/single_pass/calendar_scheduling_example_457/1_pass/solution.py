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
        if s <= last_e:  # overlap or touch
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def subtract_intervals(window, busy):
    ws, we = window
    busy = [(max(ws, s), min(we, e)) for s, e in busy if e > ws and s < we]
    busy = merge_intervals(busy)
    free = []
    cur = ws
    for s, e in busy:
        if s > cur:
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
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
window = (work_start, work_end)
duration = 30  # minutes

schedules = {
    "Andrea": [(to_minutes("09:30"), to_minutes("10:30")),
               (to_minutes("13:30"), to_minutes("14:30"))],
    "Ruth": [(to_minutes("12:30"), to_minutes("13:00")),
             (to_minutes("15:00"), to_minutes("15:30"))],
    "Steven": [(to_minutes("10:00"), to_minutes("10:30")),
               (to_minutes("11:00"), to_minutes("11:30")),
               (to_minutes("12:00"), to_minutes("12:30")),
               (to_minutes("13:30"), to_minutes("14:00")),
               (to_minutes("15:00"), to_minutes("16:00"))],
    "Grace": [],
    "Kyle": [(to_minutes("09:00"), to_minutes("09:30")),
             (to_minutes("10:30"), to_minutes("12:00")),
             (to_minutes("12:30"), to_minutes("13:00")),
             (to_minutes("13:30"), to_minutes("15:00")),
             (to_minutes("15:30"), to_minutes("16:00")),
             (to_minutes("16:30"), to_minutes("17:00"))],
    "Elijah": [(to_minutes("09:00"), to_minutes("11:00")),
               (to_minutes("11:30"), to_minutes("13:00")),
               (to_minutes("13:30"), to_minutes("14:00")),
               (to_minutes("15:30"), to_minutes("16:00")),
               (to_minutes("16:30"), to_minutes("17:00"))],
    "Lori": [(to_minutes("09:00"), to_minutes("09:30")),
             (to_minutes("10:00"), to_minutes("11:30")),
             (to_minutes("12:00"), to_minutes("13:30")),
             (to_minutes("14:00"), to_minutes("16:00")),
             (to_minutes("16:30"), to_minutes("17:00"))],
}

# Compute free intervals for each participant within working hours
free_per_person = [
    subtract_intervals(window, schedules[name]) for name in schedules
]

# Find common free intervals across all participants
common_free = reduce(intersect_two, free_per_person)

# Find the earliest slot that fits the duration
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
    print(day)
    print("{No available slot}")