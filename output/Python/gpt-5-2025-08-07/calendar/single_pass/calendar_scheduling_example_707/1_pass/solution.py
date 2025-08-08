from datetime import datetime, timedelta

# Helper functions
def t2m(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def m2t(m):
    return f"{m//60:02d}:{m%60:02d}"

def merge(intervals):
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for s,e in intervals[1:]:
        ls,le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s,e))
    return merged

def invert(busy, work_start, work_end):
    busy = merge([i for i in busy if i[1] > work_start and i[0] < work_end])
    free = []
    cur = work_start
    for s,e in busy:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < work_end:
        free.append((cur, work_end))
    return free

def intersect(a, b):
    i, j = 0, 0
    out = []
    a = sorted(a)
    b = sorted(b)
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

# Inputs
work_start, work_end = t2m("09:00"), t2m("17:00")
duration = 30  # minutes

days = ["Monday", "Tuesday", "Wednesday"]

ryan_busy = {
    "Monday":    [("09:30","10:00"), ("11:00","12:00"), ("13:00","13:30"), ("15:30","16:00")],
    "Tuesday":   [("11:30","12:30"), ("15:30","16:00")],
    "Wednesday": [("12:00","13:00"), ("15:30","16:00"), ("16:30","17:00")],
}

adam_busy = {
    "Monday":    [("09:00","10:30"), ("11:00","13:30"), ("14:00","16:00"), ("16:30","17:00")],
    "Tuesday":   [("09:00","10:00"), ("10:30","15:30"), ("16:00","17:00")],
    "Wednesday": [("09:00","09:30"), ("10:00","11:00"), ("11:30","14:30"), ("15:00","15:30"), ("16:00","16:30")],
}

# Convert to minutes
rb = {d: [(t2m(s), t2m(e)) for s,e in ryan_busy.get(d, [])] for d in days}
ab = {d: [(t2m(s), t2m(e)) for s,e in adam_busy.get(d, [])] for d in days}

# Constraints:
# - Ryan cannot meet on Wednesday
allowed_days = ["Monday", "Tuesday"]  # exclude Wednesday

# Preference:
# - Adam would like to avoid Monday before 14:30
avoid_monday_before = t2m("14:30")
# - Prefer Tuesday if possible
day_priority = {"Tuesday": 1, "Monday": 2}

candidates = []

for d in allowed_days:
    r_free = invert(rb.get(d, []), work_start, work_end)
    a_free = invert(ab.get(d, []), work_start, work_end)
    common = intersect(r_free, a_free)
    # From each common interval, propose the earliest slot of required duration
    for s,e in common:
        if e - s >= duration:
            candidates.append((d, s, s + duration))

if not candidates:
    raise SystemExit("No feasible slot found")

# Rank candidates by preferences:
def score(slot):
    d, s, e = slot
    base = day_priority.get(d, 99)
    penalty = 0
    # Penalize Monday before 14:30 strongly
    if d == "Monday" and s < avoid_monday_before:
        penalty += 1000
    return (base, penalty, s, e)

best = sorted(candidates, key=score)[0]
day, start, end = best

print(f"{day} {{{m2t(start)}:{m2t(end)}}}")