# Meeting scheduler for Terry and Frances
# Goal: 30-minute meeting during 09:00-17:00, Mon-Fri, avoiding Tuesday if possible,
# and choosing the earliest available time.

WORK_START = 9 * 60   # 09:00 in minutes
WORK_END = 17 * 60    # 17:00 in minutes
DURATION = 30         # minutes

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt(m):
    return f"{m//60:02d}:{m%60:02d}"

def merge_intervals(intervals):
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

def clip_to_work_hours(intervals):
    clipped = []
    for s, e in intervals:
        s = max(s, WORK_START)
        e = min(e, WORK_END)
        if s < e:
            clipped.append((s, e))
    return merge_intervals(clipped)

def free_from_busy(busy):
    busy = clip_to_work_hours(busy)
    free = []
    cur = WORK_START
    for s, e in busy:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < WORK_END:
        free.append((cur, WORK_END))
    return free

def intersect_intervals(a, b):
    i = j = 0
    inter = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            inter.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return inter

# Busy schedules
terry_busy = {
    "Monday":    [("10:30","11:00"), ("12:30","14:00"), ("15:00","17:00")],
    "Tuesday":   [("09:30","10:00"), ("10:30","11:00"), ("14:00","14:30"), ("16:00","16:30")],
    "Wednesday": [("09:30","10:30"), ("11:00","12:00"), ("13:00","13:30"), ("15:00","16:00"), ("16:30","17:00")],
    "Thursday":  [("09:30","10:00"), ("12:00","12:30"), ("13:00","14:30"), ("16:00","16:30")],
    "Friday":    [("09:00","11:30"), ("12:00","12:30"), ("13:30","16:00"), ("16:30","17:00")],
}

frances_busy = {
    "Monday":    [("09:30","11:00"), ("11:30","13:00"), ("14:00","14:30"), ("15:00","16:00")],
    "Tuesday":   [("09:00","09:30"), ("10:00","10:30"), ("11:00","12:00"), ("13:00","14:30"), ("15:30","16:30")],
    "Wednesday": [("09:30","10:00"), ("10:30","11:00"), ("11:30","16:00"), ("16:30","17:00")],
    "Thursday":  [("11:00","12:30"), ("14:30","17:00")],
    "Friday":    [("09:30","10:30"), ("11:00","12:30"), ("13:00","16:00"), ("16:30","17:00")],
}

# Convert busy times to minutes
def convert(schedule):
    out = {}
    for day, intervals in schedule.items():
        out[day] = [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    return out

terry_busy_m = convert(terry_busy)
frances_busy_m = convert(frances_busy)

# Preference: avoid Tuesday if possible
preferred_day_order = ["Monday", "Wednesday", "Thursday", "Friday", "Tuesday"]

def find_earliest_slot():
    best = None  # (day, start)
    for day in preferred_day_order:
        tfree = free_from_busy(terry_busy_m[day])
        ffree = free_from_busy(frances_busy_m[day])
        overlap = intersect_intervals(tfree, ffree)
        for s, e in overlap:
            if e - s >= DURATION:
                # earliest slot on this day
                candidate = (day, s)
                return candidate  # earliest by our day order and time
    return best

result = find_earliest_slot()

if result is None:
    print("No available slot found.")
else:
    day, start = result
    end = start + DURATION
    print(f"{day} {{{fmt(start)}:{fmt(end)}}}")