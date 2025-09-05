from datetime import datetime, timedelta

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

def invert_within(intervals, start, end):
    # intervals are assumed merged and clipped within [start, end)
    free = []
    cur = start
    for s, e in intervals:
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

# Problem setup
work_start = to_minutes("09:00")
work_end   = to_minutes("17:00")
duration = 30  # minutes

days = ["Monday", "Tuesday", "Wednesday"]
allowed_days = set(days)

# Existing schedules (busy times) per participant per day
susan_busy = {
    "Monday":    [("12:30","13:00"), ("13:30","14:00")],
    "Tuesday":   [("11:30","12:00")],
    "Wednesday": [("09:30","10:30"), ("14:00","14:30"), ("15:30","16:30")],
}

sandra_busy = {
    "Monday":    [("09:00","13:00"), ("14:00","15:00"), ("16:00","16:30")],
    "Tuesday":   [("09:00","09:30"), ("10:30","12:00"), ("12:30","13:30"), ("14:00","14:30"), ("16:00","17:00")],
    "Wednesday": [("09:00","11:30"), ("12:00","12:30"), ("13:00","17:00")],
}

# Convert to minutes and clip/merge within work hours
def normalize(day_busy):
    m = {}
    for d in days:
        raw = [(to_minutes(s), to_minutes(e)) for s, e in day_busy.get(d, [])]
        # Clip to work window
        clipped = []
        for s, e in raw:
            if e <= work_start or s >= work_end:
                continue
            clipped.append((max(s, work_start), min(e, work_end)))
        m[d] = merge_intervals(sorted(clipped))
    return m

susan_busy_m = normalize(susan_busy)
sandra_busy_m = normalize(sandra_busy)

# Hard constraint: Sandra cannot meet on Monday after 16:00
# Enforce by marking 16:00-17:00 as busy on Monday
sixteen = to_minutes("16:00")
sandra_busy_m["Monday"] = merge_intervals(sandra_busy_m["Monday"] + [(sixteen, work_end)])

# Compute free intervals for each
def free_for(busy_map):
    free_map = {}
    for d in days:
        free_map[d] = invert_within(busy_map[d], work_start, work_end)
    return free_map

susan_free = free_for(susan_busy_m)
sandra_free = free_for(sandra_busy_m)

# Find common free slots per day
common_free = {}
for d in days:
    if d not in allowed_days:
        common_free[d] = []
        continue
    common_free[d] = intersect_intervals(susan_free[d], sandra_free[d])

# Generate candidate 30-minute slots from common intervals
def generate_slots(intervals, dur):
    slots = []
    for s, e in intervals:
        if e - s >= dur:
            slots.append((s, s + dur))
    return slots

candidates = []
for d in days:
    for s, e in generate_slots(common_free[d], duration):
        candidates.append((d, s, e))

# Preference: Susan would rather not meet on Tuesday.
# Implement by day priority: Monday (best), Wednesday (next), Tuesday (least).
day_priority = {"Monday": 0, "Wednesday": 1, "Tuesday": 2}

# Sort candidates by preference then by start time
candidates.sort(key=lambda x: (day_priority.get(x[0], 99), x[1]))

if not candidates:
    raise SystemExit("No feasible slot found, but problem statement guarantees a solution.")

chosen_day, start_m, end_m = candidates[0]
time_range = f"{to_hhmm(start_m)}:{to_hhmm(end_m)}"

# Output must include both the time range and the day of the week.
print(f"{chosen_day} {{{time_range}}}")