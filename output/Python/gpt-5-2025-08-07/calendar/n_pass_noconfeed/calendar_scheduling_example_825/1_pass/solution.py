# Meeting scheduler for Laura and Philip
# Find a 1-hour slot between 09:00-17:00 on Mon/Tue/Wed/Thu
# with the constraint that Philip cannot meet on Wednesday.
# Outputs: Day and {HH:MM:HH:MM}

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m//60:02d}:{m%60:02d}"

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

def invert_intervals(busy, work_start, work_end):
    busy = merge_intervals([i for i in busy if i[0] < work_end and i[1] > work_start])
    free = []
    curr = work_start
    for s, e in busy:
        s = max(s, work_start)
        e = min(e, work_end)
        if curr < s:
            free.append((curr, s))
        curr = max(curr, e)
    if curr < work_end:
        free.append((curr, work_end))
    return free

def intersect_two(a, b):
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

work_start = to_minutes("09:00")
work_end   = to_minutes("17:00")
duration = 60  # minutes

days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

laura_busy = {
    "Monday":    [("10:30","11:00"), ("12:30","13:00"), ("14:30","15:30"), ("16:00","17:00")],
    "Tuesday":   [("09:30","10:00"), ("11:00","11:30"), ("13:00","13:30"), ("14:30","15:00"), ("16:00","17:00")],
    "Wednesday": [("11:30","12:00"), ("12:30","13:00"), ("15:30","16:30")],
    "Thursday":  [("10:30","11:00"), ("12:00","13:30"), ("15:00","15:30"), ("16:00","16:30")],
}

philip_busy = {
    "Monday":    [("09:00","17:00")],
    "Tuesday":   [("09:00","11:00"), ("11:30","12:00"), ("13:00","13:30"), ("14:00","14:30"), ("15:00","16:30")],
    "Wednesday": [("09:00","10:00"), ("11:00","12:00"), ("12:30","16:00"), ("16:30","17:00")],
    "Thursday":  [("09:00","10:30"), ("11:00","12:30"), ("13:00","17:00")],
}

# Convert to minutes
def convert_sched(sched):
    out = {}
    for d, slots in sched.items():
        out[d] = [(to_minutes(s), to_minutes(e)) for s, e in slots]
    return out

laura_busy_m  = convert_sched(laura_busy)
philip_busy_m = convert_sched(philip_busy)

# Constraint: Philip cannot meet on Wednesday
disallowed_days = {"Wednesday"}

found = None
for day in days:
    if day in disallowed_days:
        continue
    laura_free = invert_intervals(laura_busy_m.get(day, []), work_start, work_end)
    philip_free = invert_intervals(philip_busy_m.get(day, []), work_start, work_end)
    common = intersect_two(laura_free, philip_free)
    # Find first slot with required duration
    for s, e in common:
        if e - s >= duration:
            start = s
            end = s + duration
            found = (day, start, end)
            break
    if found:
        break

if not found:
    raise SystemExit("No valid slot found (but problem guarantees a solution).")

day, start, end = found
print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")