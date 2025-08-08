from datetime import datetime, timedelta

# Helper functions
def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def clip(interval, start, end):
    s, e = interval
    s = max(s, start)
    e = min(e, end)
    if s < e:
        return (s, e)
    return None

def merge_intervals(intervals):
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def earliest_slot(day, calendars, work_start, work_end, duration_minutes):
    # Gather and merge busy intervals for all participants on the given day
    busy = []
    for cal in calendars:
        for s, e in cal.get(day, []):
            clipped = clip((s, e), work_start, work_end)
            if clipped:
                busy.append(clipped)
    busy = merge_intervals(busy)

    # Find first free slot of required duration
    prev_end = work_start
    for s, e in busy:
        if s - prev_end >= duration_minutes:
            return prev_end, prev_end + duration_minutes
        prev_end = max(prev_end, e)
    if work_end - prev_end >= duration_minutes:
        return prev_end, prev_end + duration_minutes
    return None

# Data setup
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes

days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Calendars defined as minutes-from-midnight intervals per day
cheryl_calendar = {
    # Cheryl is free all week within work hours, so no busy blocks
}

james_calendar = {
    "Monday": [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("10:30"), to_minutes("11:00")),
        (to_minutes("12:30"), to_minutes("13:00")),
        (to_minutes("14:30"), to_minutes("15:30")),
        (to_minutes("16:30"), to_minutes("17:00")),
    ],
    "Tuesday": [
        (to_minutes("09:00"), to_minutes("11:00")),
        (to_minutes("11:30"), to_minutes("12:00")),
        (to_minutes("12:30"), to_minutes("15:30")),
        (to_minutes("16:00"), to_minutes("17:00")),
    ],
    "Wednesday": [
        (to_minutes("10:00"), to_minutes("11:00")),
        (to_minutes("12:00"), to_minutes("13:00")),
        (to_minutes("13:30"), to_minutes("16:00")),
    ],
    "Thursday": [
        (to_minutes("09:30"), to_minutes("11:30")),
        (to_minutes("12:00"), to_minutes("12:30")),
        (to_minutes("13:00"), to_minutes("13:30")),
        (to_minutes("14:00"), to_minutes("14:30")),
        (to_minutes("16:30"), to_minutes("17:00")),
    ],
}

# Preference: Cheryl would rather not meet on Wednesday and Thursday
avoid_days = {"Wednesday", "Thursday"}
preferred_days = [d for d in days if d not in avoid_days] + [d for d in days if d in avoid_days]

# Find earliest feasible slot honoring day preference order
calendars = [cheryl_calendar, james_calendar]
meeting_day = None
meeting_time = None

for day in preferred_days:
    slot = earliest_slot(day, calendars, work_start, work_end, duration)
    if slot:
        meeting_day = day
        meeting_time = slot
        break

if meeting_day and meeting_time:
    start, end = meeting_time
    # Output: day of week and time range in HH:MM:HH:MM
    print(meeting_day)
    print(f"{fmt(start)}:{fmt(end)}")
else:
    # Fallback (should not happen per problem statement)
    print("No available slot found")
    print("00:00:00:00")