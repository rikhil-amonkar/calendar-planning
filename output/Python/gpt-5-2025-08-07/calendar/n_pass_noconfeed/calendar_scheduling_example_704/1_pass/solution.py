from datetime import timedelta

# Meeting requirements
MEETING_DURATION_MIN = 30
WORK_START = "09:00"
WORK_END = "17:00"
DAYS = ["Monday", "Tuesday", "Wednesday"]

# Preferences (soft): lower is better
DAY_PENALTY = {
    "Monday": 0,        # No one objected
    "Tuesday": 1,       # Samuel would like to avoid
    "Wednesday": 1,     # Larry would rather not
}

def to_minutes(hhmm):
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

WORK_START_MIN = to_minutes(WORK_START)
WORK_END_MIN = to_minutes(WORK_END)

# Participants' calendars (busy times) per day, as [("HH:MM","HH:MM"), ...]
calendars = {
    "Larry": {
        # Larry's calendar is wide open (no busy blocks within work hours)
        "Monday": [],
        "Tuesday": [],
        "Wednesday": [],
    },
    "Samuel": {
        "Monday": [("10:30","11:00"), ("12:00","12:30"), ("13:00","15:00"), ("15:30","16:30")],
        "Tuesday": [("09:00","12:00"), ("14:00","15:30"), ("16:30","17:00")],
        "Wednesday": [("10:30","11:00"), ("11:30","12:00"), ("12:30","13:00"), ("14:00","14:30"), ("15:00","16:00")],
    }
}

def normalize_busy(busy_blocks):
    # Convert to minutes and merge overlapping
    intervals = sorted([(to_minutes(s), to_minutes(e)) for s, e in busy_blocks], key=lambda x: x[0])
    merged = []
    for s, e in intervals:
        if not merged or s > merged[-1][1]:
            merged.append([s, e])
        else:
            merged[-1][1] = max(merged[-1][1], e)
    return [(max(WORK_START_MIN, s), min(WORK_END_MIN, e)) for s, e in merged if min(WORK_END_MIN, e) > max(WORK_START_MIN, s)]

def free_from_busy(busy_intervals):
    # Complement of busy within work window [WORK_START_MIN, WORK_END_MIN)
    free = []
    cur = WORK_START_MIN
    for s, e in busy_intervals:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < WORK_END_MIN:
        free.append((cur, WORK_END_MIN))
    return free

def intersect_intervals(a, b):
    i, j = 0, 0
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

def group_free_on_day(day):
    # Start with universal free = work window
    group_free = [(WORK_START_MIN, WORK_END_MIN)]
    for person, sched in calendars.items():
        busy = normalize_busy(sched.get(day, []))
        free = free_from_busy(busy)
        group_free = intersect_intervals(group_free, free)
        if not group_free:
            break
    return group_free

def earliest_slot(day, duration_min):
    free_blocks = group_free_on_day(day)
    for s, e in free_blocks:
        if e - s >= duration_min:
            return (s, s + duration_min)
    return None

candidates = []
for day in DAYS:
    slot = earliest_slot(day, MEETING_DURATION_MIN)
    if slot:
        start, end = slot
        # Sort by absolute start time first (earliest availability),
        # then by day penalty (respect soft preferences when times are equal)
        candidates.append((day, start, end, DAY_PENALTY.get(day, 0)))

# Choose the best candidate
if not candidates:
    raise SystemExit("No viable meeting slot found.")
candidates.sort(key=lambda x: (x[1], x[3]))  # earliest time, then lowest penalty
best_day, start_min, end_min, _ = candidates[0]

time_range = f"{to_hhmm(start_min)}:{to_hhmm(end_min)}"
print(f"{best_day} {{{time_range}}}")