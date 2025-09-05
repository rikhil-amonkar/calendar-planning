from datetime import datetime, timedelta

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    return f"{m//60:02d}:{m%60:02d}"

def subtract_busy_from_work(work_interval, busy_intervals):
    ws, we = work_interval
    busy = sorted(busy_intervals)
    free = []
    cur = ws
    for bs, be in busy:
        if be <= cur:
            continue
        if bs > cur:
            free.append((cur, min(bs, we)))
        cur = max(cur, be)
        if cur >= we:
            break
    if cur < we:
        free.append((cur, we))
    # Filter out non-positive intervals
    return [(s, e) for s, e in free if e - s > 0]

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

def earliest_meeting_slot(common_free, duration):
    # Return the earliest (start, end) that fits duration
    for s, e in common_free:
        if e - s >= duration:
            return (s, s + duration)
    return None

# Parameters
meeting_duration = 60  # minutes
work_hours = (to_minutes("09:00"), to_minutes("17:00"))

# Schedules
russell_busy = {
    "Monday": [(to_minutes("10:30"), to_minutes("11:00"))],
    "Tuesday": [(to_minutes("13:00"), to_minutes("13:30"))],
}

alexander_busy = {
    "Monday": [
        (to_minutes("09:00"), to_minutes("11:30")),
        (to_minutes("12:00"), to_minutes("14:30")),
        (to_minutes("15:00"), to_minutes("17:00")),
    ],
    "Tuesday": [
        (to_minutes("09:00"), to_minutes("10:00")),
        (to_minutes("13:00"), to_minutes("14:00")),
        (to_minutes("15:00"), to_minutes("15:30")),
        (to_minutes("16:00"), to_minutes("16:30")),
    ],
}

# Preference: Russell would rather not meet on Tuesday before 13:30
tuesday_preferred_start = to_minutes("13:30")

days = ["Monday", "Tuesday"]
proposal = None

for day in days:
    r_free = subtract_busy_from_work(work_hours, russell_busy.get(day, []))
    a_free = subtract_busy_from_work(work_hours, alexander_busy.get(day, []))
    common = intersect_intervals(r_free, a_free)

    if day == "Tuesday":
        # Try to respect preference: filter common intervals to start at/after 13:30 if possible
        preferred_common = []
        for s, e in common:
            if e <= tuesday_preferred_start:
                continue
            preferred_common.append((max(s, tuesday_preferred_start), e))

        slot = earliest_meeting_slot(preferred_common, meeting_duration)
        if slot is None:
            # Fallback to any Tuesday slot if none meet the preference
            slot = earliest_meeting_slot(common, meeting_duration)
    else:
        slot = earliest_meeting_slot(common, meeting_duration)

    if slot:
        proposal = (day, slot[0], slot[1])
        break

if proposal:
    day, start, end = proposal
    print(day)
    print(f"{to_hhmm(start)}:{to_hhmm(end)}")
else:
    # Per prompt, a solution exists; this is a safety fallback.
    print("No available slot found")
    print("00:00:00:00")