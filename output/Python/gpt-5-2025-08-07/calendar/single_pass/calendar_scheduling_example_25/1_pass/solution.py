from itertools import reduce

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_str(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    intervals = sorted(intervals, key=lambda x: x[0])
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:  # overlap or touching
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def subtract_intervals(window, busy):
    # window: (start, end), busy: list of (start, end)
    ws, we = window
    busy = merge_intervals([b for b in busy if not (b[1] <= ws or b[0] >= we)])
    free = []
    cur = ws
    for s, e in busy:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
        if cur >= we:
            break
    if cur < we:
        free.append((cur, we))
    return free

def intersect_two(a, b):
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

# Meeting parameters
day = "Monday"
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
window = (work_start, work_end)
duration = 60  # minutes

# Participants' busy schedules (Monday)
busy_raw = {
    "Anthony": [("09:30", "10:00"), ("12:00", "13:00"), ("16:00", "16:30")],
    "Pamela":  [("09:30", "10:00"), ("16:30", "17:00")],
    "Zachary": [("09:00", "11:30"), ("12:00", "12:30"), ("13:00", "13:30"),
                ("14:30", "15:00"), ("16:00", "17:00")],
}

# Pamela's preference: do not meet after 14:30 (meeting must end by 14:30)
latest_end_limit = to_minutes("14:30")

# Convert busy times to minutes
busy_minutes = {
    person: [(to_minutes(s), to_minutes(e)) for s, e in slots]
    for person, slots in busy_raw.items()
}

# Compute each participant's free intervals within work window
free_by_person = {
    person: subtract_intervals(window, slots)
    for person, slots in busy_minutes.items()
}

# Compute common free intervals
common_free = reduce(intersect_two, free_by_person.values())

# Apply latest end limit due to Pamela's preference and find earliest feasible slot
proposed = None
for s, e in common_free:
    capped_end = min(e, latest_end_limit)
    if capped_end - s >= duration:
        proposed_start = s
        proposed_end = proposed_start + duration
        if proposed_end <= capped_end:
            proposed = (proposed_start, proposed_end)
            break

if proposed:
    start_str = to_str(proposed[0])
    end_str = to_str(proposed[1])
    print(f"{day} {{{start_str}:{end_str}}}")
else:
    print(f"{day} {{No suitable time found}}")