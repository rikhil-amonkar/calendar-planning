from datetime import datetime, timedelta

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def normalize_intervals(intervals):
    intervals = sorted((start, end) for start, end in intervals if start < end)
    merged = []
    for s, e in intervals:
        if not merged or s > merged[-1][1]:
            merged.append([s, e])
        else:
            merged[-1][1] = max(merged[-1][1], e)
    return [(s, e) for s, e in merged]

def invert_busy_to_free(busy, work_start, work_end):
    busy = normalize_intervals([(max(work_start, s), min(work_end, e)) for s, e in busy if e > work_start and s < work_end])
    free = []
    curr = work_start
    for s, e in busy:
        if s > curr:
            free.append((curr, s))
        curr = max(curr, e)
    if curr < work_end:
        free.append((curr, work_end))
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

# Inputs
days = ["Monday", "Tuesday", "Wednesday"]
work_hours = ("09:00", "17:00")
duration_minutes = 30

# Participants' calendars (busy times)
larry_busy = {
    "Monday": [],
    "Tuesday": [],
    "Wednesday": []
}
samuel_busy = {
    "Monday": [("10:30","11:00"), ("12:00","12:30"), ("13:00","15:00"), ("15:30","16:30")],
    "Tuesday": [("09:00","12:00"), ("14:00","15:30"), ("16:30","17:00")],
    "Wednesday": [("10:30","11:00"), ("11:30","12:00"), ("12:30","13:00"), ("14:00","14:30"), ("15:00","16:00")]
}

# Convert to minutes
work_start, work_end = map(to_minutes, work_hours)
larry_busy_m = {d: [(to_minutes(s), to_minutes(e)) for s, e in larry_busy.get(d, [])] for d in days}
samuel_busy_m = {d: [(to_minutes(s), to_minutes(e)) for s, e in samuel_busy.get(d, [])] for d in days}

# Preferences (soft): days each participant would rather avoid
avoid = {
    "Larry": {"Wednesday"},
    "Samuel": {"Tuesday"}
}

# Compute day preference ranking: fewer avoids preferred; tie by weekday order
day_scores = {}
for idx, d in enumerate(days):
    score = 0
    if d in avoid["Larry"]:
        score += 1
    if d in avoid["Samuel"]:
        score += 1
    day_scores[d] = (score, idx)

preferred_day_order = sorted(days, key=lambda d: day_scores[d])

# Find earliest feasible slot respecting preferences and time
for day in preferred_day_order:
    # Free intervals for each participant
    larry_free = invert_busy_to_free(larry_busy_m.get(day, []), work_start, work_end)
    samuel_free = invert_busy_to_free(samuel_busy_m.get(day, []), work_start, work_end)

    # Intersection of availability
    common = intersect_intervals(larry_free, samuel_free)

    # Earliest slot of required duration
    for s, e in common:
        if e - s >= duration_minutes:
            start_str = to_hhmm(s)
            end_str = to_hhmm(s + duration_minutes)
            print(f"{day} {{{start_str}:{end_str}}}")
            raise SystemExit

# Fallback (should not happen per problem statement)
print("No available slot found")