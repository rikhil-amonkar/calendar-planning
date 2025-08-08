# Meeting scheduler for Betty and Megan

WORK_START = 9 * 60   # 09:00 in minutes
WORK_END = 17 * 60    # 17:00 in minutes
MEETING_DURATION = 60 # in minutes

days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

def to_minutes(hh_mm):
    h, m = map(int, hh_mm.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        ls, le = merged[-1]
        if s <= le:  # overlap or touch
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def invert_intervals(busy, start, end):
    busy = merge_intervals([(max(start, s), min(end, e)) for s, e in busy if e > start and s < end])
    free = []
    prev_end = start
    for s, e in busy:
        if s > prev_end:
            free.append((prev_end, s))
        prev_end = max(prev_end, e)
    if prev_end < end:
        free.append((prev_end, end))
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

# Busy schedules (in minutes from midnight)
betty_busy = {
    "Monday":    [(10*60, 10*60+30), (11*60+30, 12*60+30), (16*60, 16*60+30)],
    "Tuesday":   [(9*60+30, 10*60), (10*60+30, 11*60), (12*60, 12*60+30), (13*60+30, 15*60), (16*60+30, 17*60)],
    "Wednesday": [(13*60+30, 14*60), (14*60+30, 15*60)],
    "Thursday":  [],
    "Friday":    [(9*60, 10*60), (11*60+30, 12*60), (12*60+30, 13*60), (14*60+30, 15*60)],
}
megan_busy = {
    "Monday":    [(9*60, 17*60)],
    "Tuesday":   [(9*60, 9*60+30), (10*60, 10*60+30), (12*60, 14*60), (15*60, 15*60+30), (16*60, 16*60+30)],
    "Wednesday": [(9*60+30, 10*60+30), (11*60, 11*60+30), (12*60+30, 13*60), (13*60+30, 14*60+30), (15*60+30, 17*60)],
    "Thursday":  [(9*60, 10*60+30), (11*60+30, 14*60), (14*60+30, 15*60), (15*60+30, 16*60+30)],
    "Friday":    [(9*60, 17*60)],
}

# Unavailable days (constraints)
unavailable = {
    "Betty": {"Wednesday", "Thursday"},
    "Megan": set(),
}

def find_meeting():
    for day in days:
        # Respect unavailable constraints
        if any(day in unavailable.get(person, set()) for person in ["Betty", "Megan"]):
            continue

        betty_free = invert_intervals(betty_busy.get(day, []), WORK_START, WORK_END)
        megan_free = invert_intervals(megan_busy.get(day, []), WORK_START, WORK_END)

        overlap = intersect_intervals(betty_free, megan_free)
        for s, e in overlap:
            if e - s >= MEETING_DURATION:
                start = s
                end = s + MEETING_DURATION
                return day, start, end
    return None, None, None

day, start, end = find_meeting()
if day is None:
    print("No available slot found")
else:
    print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")