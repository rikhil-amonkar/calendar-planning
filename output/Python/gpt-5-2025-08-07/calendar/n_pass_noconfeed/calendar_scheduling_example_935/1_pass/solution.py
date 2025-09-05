from datetime import datetime

WORK_START = "09:00"
WORK_END = "17:00"
MEETING_MINUTES = 30

# Helper functions
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
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def complement_within(day_busy, start_min, end_min):
    busy = merge_intervals(day_busy)
    free = []
    curr = start_min
    for s, e in busy:
        if s > curr:
            free.append((curr, s))
        curr = max(curr, e)
    if curr < end_min:
        free.append((curr, end_min))
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

# Data
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
preference_order = ["Monday", "Wednesday", "Thursday", "Friday", "Tuesday"]  # avoid Tuesday if possible

terry_busy = {
    "Monday":    [("10:30","11:00"),("12:30","14:00"),("15:00","17:00")],
    "Tuesday":   [("09:30","10:00"),("10:30","11:00"),("14:00","14:30"),("16:00","16:30")],
    "Wednesday": [("09:30","10:30"),("11:00","12:00"),("13:00","13:30"),("15:00","16:00"),("16:30","17:00")],
    "Thursday":  [("09:30","10:00"),("12:00","12:30"),("13:00","14:30"),("16:00","16:30")],
    "Friday":    [("09:00","11:30"),("12:00","12:30"),("13:30","16:00"),("16:30","17:00")],
}

frances_busy = {
    "Monday":    [("09:30","11:00"),("11:30","13:00"),("14:00","14:30"),("15:00","16:00")],
    "Tuesday":   [("09:00","09:30"),("10:00","10:30"),("11:00","12:00"),("13:00","14:30"),("15:30","16:30")],
    "Wednesday": [("09:30","10:00"),("10:30","11:00"),("11:30","16:00"),("16:30","17:00")],
    "Thursday":  [("11:00","12:30"),("14:30","17:00")],
    "Friday":    [("09:30","10:30"),("11:00","12:30"),("13:00","16:00"),("16:30","17:00")],
}

# Convert busy times to minutes
def convert_schedule(sched):
    out = {}
    for d, intervals in sched.items():
        out[d] = [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    return out

terry_busy_m = convert_schedule(terry_busy)
frances_busy_m = convert_schedule(frances_busy)
work_start_m = to_minutes(WORK_START)
work_end_m = to_minutes(WORK_END)

def earliest_slot_for_day(day):
    t_free = complement_within(terry_busy_m[day], work_start_m, work_end_m)
    f_free = complement_within(frances_busy_m[day], work_start_m, work_end_m)
    overlap = intersect_intervals(t_free, f_free)
    for s, e in overlap:
        if e - s >= MEETING_MINUTES:
            return s, s + MEETING_MINUTES
    return None

# First, try preferred (non-Tuesday) days, then Tuesday if necessary
chosen = None
chosen_day = None

for day in preference_order:
    slot = earliest_slot_for_day(day)
    if slot:
        chosen = slot
        chosen_day = day
        # If it's Tuesday, only choose it if no other day worked; since order puts Tue last, this is fine.
        break

if not chosen:
    raise RuntimeError("No available slot found, though one was expected.")

start_m, end_m = chosen
time_range = f"{to_hhmm(start_m)}:{to_hhmm(end_m)}"

# Output: include both day and time range
print(f"{chosen_day} {time_range}")