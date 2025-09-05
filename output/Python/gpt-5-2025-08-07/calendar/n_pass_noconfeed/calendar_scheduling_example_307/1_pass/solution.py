# Meeting scheduler for Monday between 09:00 and 17:00
# Participants: Ronald, Stephen, Brittany, Dorothy, Rebecca, Jordan
# Duration: 30 minutes

def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    return f"{m//60:02d}:{m%60:02d}"

def invert_busy(busy, start, end):
    busy = sorted(busy)
    free = []
    cur = start
    for s, e in busy:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
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

day = "Monday"
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
duration = 30

# Busy schedules (inclusive of Monday working hours)
schedules_busy = {
    "Ronald": [],
    "Stephen": [
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
    ],
    "Brittany": [
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00")),
    ],
    "Dorothy": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("17:00")),
    ],
    "Rebecca": [
        (time_to_minutes("09:30"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("17:00")),
    ],
    "Jordan": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("10:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("12:00")),
        (time_to_minutes("13:00"), time_to_minutes("15:00")),
        (time_to_minutes("15:30"), time_to_minutes("16:30")),
    ],
}

# Compute free intervals for each participant
free_intervals = []
for person, busy in schedules_busy.items():
    free_intervals.append(invert_busy(busy, work_start, work_end))

# Intersect all free intervals
from functools import reduce
common_free = reduce(intersect_intervals, free_intervals)

# Find earliest slot that fits the duration
start_time, end_time = None, None
for s, e in common_free:
    if e - s >= duration:
        start_time = s
        end_time = s + duration
        break

# Output
if start_time is None:
    raise RuntimeError("No common slot found, but the problem statement guarantees one exists.")

print(f"{{{minutes_to_time(start_time)}:{minutes_to_time(end_time)}}}")
print(day)