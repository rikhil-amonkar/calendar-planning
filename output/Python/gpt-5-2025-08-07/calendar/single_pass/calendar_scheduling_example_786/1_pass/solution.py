from datetime import datetime, timedelta

# Helper functions
def to_minutes(tstr):
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def to_timestr(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def normalize_intervals(intervals):
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

def subtract_intervals(full_start, full_end, busy_intervals):
    busy = normalize_intervals([(max(full_start, s), min(full_end, e)) for s, e in busy_intervals if e > full_start and s < full_end])
    free = []
    cur = full_start
    for s, e in busy:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < full_end:
        free.append((cur, full_end))
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

# Schedules
work_hours = (to_minutes("09:00"), to_minutes("17:00"))
duration = 30  # minutes

days = ["Monday", "Tuesday", "Wednesday"]

amy_busy = {
    "Monday": [],
    "Tuesday": [],
    "Wednesday": [(to_minutes("11:00"), to_minutes("11:30")),
                  (to_minutes("13:30"), to_minutes("14:00"))],
}

pamela_busy = {
    "Monday": [(to_minutes("09:00"), to_minutes("10:30")),
               (to_minutes("11:00"), to_minutes("16:30"))],
    "Tuesday": [(to_minutes("09:00"), to_minutes("09:30")),
                (to_minutes("10:00"), to_minutes("17:00"))],
    "Wednesday": [(to_minutes("09:00"), to_minutes("09:30")),
                  (to_minutes("10:00"), to_minutes("11:00")),
                  (to_minutes("11:30"), to_minutes("13:30")),
                  (to_minutes("14:30"), to_minutes("15:00")),
                  (to_minutes("16:00"), to_minutes("16:30"))],
}

# Preferences (soft):
# - Avoid Monday for Pamela (stronger penalty)
# - Avoid Tuesday/Wednesday before 16:00 (lighter penalty)
def preference_penalty(day, start_min):
    penalty = 0
    if day == "Monday":
        penalty += 2
    if day in ("Tuesday", "Wednesday") and start_min < to_minutes("16:00"):
        penalty += 1
    return penalty

# Compute free intervals per day for both participants
amy_free = {d: subtract_intervals(*work_hours, amy_busy.get(d, [])) for d in days}
pamela_free = {d: subtract_intervals(*work_hours, pamela_busy.get(d, [])) for d in days}

# Find all candidate 30-minute slots
candidates = []
for day in days:
    overlap = intersect_intervals(amy_free[day], pamela_free[day])
    # Break into 30-minute slots aligned to 30-minute boundaries
    for s, e in overlap:
        start = s
        # align to 30-min boundary if needed
        if start % 30 != 0:
            start += (30 - start % 30)
        while start + duration <= e:
            end = start + duration
            candidates.append((day, start, end))
            start += 30  # next 30-min block

# Choose best candidate by preference, then earliest time, then day order
best = None
for cand in candidates:
    day, s, e = cand
    pen = preference_penalty(day, s)
    key = (pen, s, days.index(day))
    if best is None or key < best[0]:
        best = (key, cand)

# Output result
if best is None:
    # Fallback (shouldn't happen per problem statement)
    print("No available slot")
else:
    _, (day, s, e) = best
    print(f"{to_timestr(s)}:{to_timestr(e)}")
    print(day)