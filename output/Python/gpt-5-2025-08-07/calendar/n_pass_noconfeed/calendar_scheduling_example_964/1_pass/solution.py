from datetime import datetime, timedelta

# Helper functions
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

def invert_intervals(busy, work_window):
    ws, we = work_window
    if ws >= we:
        return []
    busy = merge_intervals([(max(ws, s), min(we, e)) for s, e in busy if e > ws and s < we])
    free = []
    cursor = ws
    for s, e in busy:
        if s > cursor:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < we:
        free.append((cursor, we))
    return free

def intersect_intervals(a, b):
    i, j = 0, 0
    out = []
    while i < len(a) and j < len(b):
        s1, e1 = a[i]
        s2, e2 = b[j]
        s, e = max(s1, s2), min(e1, e2)
        if s < e:
            out.append((s, e))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return out

def first_slot(intervals, duration):
    for s, e in intervals:
        if e - s >= duration:
            return (s, s + duration)
    return None

# Data
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
WORK_START, WORK_END = to_minutes("09:00"), to_minutes("17:00")
WORK_WINDOW = (WORK_START, WORK_END)
MEETING_DURATION = 60  # minutes

betty_busy = {
    "Monday":   [(to_minutes("10:00"), to_minutes("10:30")),
                 (to_minutes("11:30"), to_minutes("12:30")),
                 (to_minutes("16:00"), to_minutes("16:30"))],
    "Tuesday":  [(to_minutes("09:30"), to_minutes("10:00")),
                 (to_minutes("10:30"), to_minutes("11:00")),
                 (to_minutes("12:00"), to_minutes("12:30")),
                 (to_minutes("13:30"), to_minutes("15:00")),
                 (to_minutes("16:30"), to_minutes("17:00"))],
    "Wednesday":[(to_minutes("13:30"), to_minutes("14:00")),
                 (to_minutes("14:30"), to_minutes("15:00"))],
    "Thursday": [],
    "Friday":   [(to_minutes("09:00"), to_minutes("10:00")),
                 (to_minutes("11:30"), to_minutes("12:00")),
                 (to_minutes("12:30"), to_minutes("13:00")),
                 (to_minutes("14:30"), to_minutes("15:00"))],
}

megan_busy = {
    "Monday":   [(to_minutes("09:00"), to_minutes("17:00"))],
    "Tuesday":  [(to_minutes("09:00"), to_minutes("09:30")),
                 (to_minutes("10:00"), to_minutes("10:30")),
                 (to_minutes("12:00"), to_minutes("14:00")),
                 (to_minutes("15:00"), to_minutes("15:30")),
                 (to_minutes("16:00"), to_minutes("16:30"))],
    "Wednesday":[(to_minutes("09:30"), to_minutes("10:30")),
                 (to_minutes("11:00"), to_minutes("11:30")),
                 (to_minutes("12:30"), to_minutes("13:00")),
                 (to_minutes("13:30"), to_minutes("14:30")),
                 (to_minutes("15:30"), to_minutes("17:00"))],
    "Thursday": [(to_minutes("09:00"), to_minutes("10:30")),
                 (to_minutes("11:30"), to_minutes("14:00")),
                 (to_minutes("14:30"), to_minutes("15:00")),
                 (to_minutes("15:30"), to_minutes("16:30"))],
    "Friday":   [(to_minutes("09:00"), to_minutes("17:00"))],
}

# Constraints: Betty cannot meet on Wednesday and Thursday
betty_allowed_days = {"Monday", "Tuesday", "Friday"}
megan_allowed_days = set(days)  # no day-level restrictions provided
allowed_days = [d for d in days if d in betty_allowed_days and d in megan_allowed_days]

# Find earliest feasible slot
for day in allowed_days:
    b_busy = betty_busy.get(day, [])
    m_busy = megan_busy.get(day, [])
    b_free = invert_intervals(b_busy, WORK_WINDOW)
    m_free = invert_intervals(m_busy, WORK_WINDOW)
    common = intersect_intervals(b_free, m_free)
    slot = first_slot(common, MEETING_DURATION)
    if slot:
        start, end = slot
        start_str, end_str = to_hhmm(start), to_hhmm(end)
        print(f"{day} {{{start_str}:{end_str}}}")
        break