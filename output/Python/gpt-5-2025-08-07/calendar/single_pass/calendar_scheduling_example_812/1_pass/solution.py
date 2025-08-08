from datetime import datetime

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time_str(minutes):
    return f"{minutes//60:02d}:{minutes%60:02d}"

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

def invert_intervals(busy, start, end):
    busy = [(max(start, s), min(end, e)) for s, e in busy if e > start and s < end]
    busy = merge_intervals(busy)
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

# Work hours and meeting duration
WORK_START = to_minutes("09:00")
WORK_END = to_minutes("17:00")
DURATION = 30  # minutes

days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Participants' busy schedules
mary_busy = {
    "Monday": [],
    "Tuesday": [("10:00","10:30"), ("15:30","16:00")],
    "Wednesday": [("09:30","10:00"), ("15:00","15:30")],
    "Thursday": [("09:00","10:00"), ("10:30","11:30")],
}
alexis_busy = {
    "Monday": [("09:00","10:00"), ("10:30","12:00"), ("12:30","16:30")],
    "Tuesday": [("09:00","10:00"), ("10:30","11:30"), ("12:00","15:30"), ("16:00","17:00")],
    "Wednesday": [("09:00","11:00"), ("11:30","17:00")],
    "Thursday": [("10:00","12:00"), ("14:00","14:30"), ("15:30","16:00"), ("16:30","17:00")],
}

# Convert to minutes
def convert_schedule(sched):
    out = {}
    for d, intervals in sched.items():
        out[d] = [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    return out

mary_busy_m = convert_schedule(mary_busy)
alexis_busy_m = convert_schedule(alexis_busy)

# Find earliest mutual availability
for day in days:
    # Compute free intervals for each participant
    mary_free = invert_intervals(mary_busy_m.get(day, []), WORK_START, WORK_END)
    alexis_free = invert_intervals(alexis_busy_m.get(day, []), WORK_START, WORK_END)

    # Intersect free intervals across participants
    mutual_free = intersect_intervals(mary_free, alexis_free)

    # Find earliest slot of required duration
    for s, e in mutual_free:
        if e - s >= DURATION:
            start = s
            end = s + DURATION
            print(f"{day} {{{to_time_str(start)}:{to_time_str(end)}}}")
            raise SystemExit

# If somehow not found (problem statement guarantees a solution)
print("No available slot found")