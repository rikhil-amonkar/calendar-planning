def time_to_minutes(t):
    """Convert time string 'HH:MM' to minutes since midnight."""
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes since midnight to time string 'HH:MM'."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy, work_start, work_end):
    """Given a list of busy intervals (each a tuple of start and end in minutes)
    and working hours, return a list of free intervals."""
    free = []
    current = work_start
    # Sort busy intervals by start time
    busy_sorted = sorted(busy, key=lambda interval: interval[0])
    for start, end in busy_sorted:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """Intersect two lists of intervals. Return list of intervals that are in both."""
    intersections = []
    for s1, e1 in intervals1:
        for s2, e2 in intervals2:
            start = max(s1, s2)
            end = min(e1, e2)
            if start < end:
                intersections.append((start, end))
    return intersections

# Define working hours and meeting duration (in minutes)
WORK_START = time_to_minutes("09:00")
WORK_END   = time_to_minutes("17:00")
MEETING_DURATION = 60  # minutes

# Busy schedules for each participant (times in HH:MM)
betty_busy_str = {
    "Monday":    [("10:00","10:30"), ("11:30","12:30"), ("16:00","16:30")],
    "Tuesday":   [("9:30","10:00"), ("10:30","11:00"), ("12:00","12:30"), ("13:30","15:00"), ("16:30","17:00")],
    "Wednesday": [("13:30","14:00"), ("14:30","15:00")],
    "Friday":    [("9:00","10:00"), ("11:30","12:00"), ("12:30","13:00"), ("14:30","15:00")]
}

megan_busy_str = {
    "Monday":    [("9:00","17:00")],
    "Tuesday":   [("9:00","9:30"), ("10:00","10:30"), ("12:00","14:00"), ("15:00","15:30"), ("16:00","16:30")],
    "Wednesday": [("9:30","10:30"), ("11:00","11:30"), ("12:30","13:00"), ("13:30","14:30"), ("15:30","17:00")],
    "Thursday":  [("9:00","10:30"), ("11:30","14:00"), ("14:30","15:00"), ("15:30","16:30")],
    "Friday":    [("9:00","17:00")]
}

# Convert the busy times to minutes
def convert_schedule(schedule_str):
    schedule = {}
    for day, intervals in schedule_str.items():
        schedule[day] = []
        for start, end in intervals:
            schedule[day].append((time_to_minutes(start), time_to_minutes(end)))
    return schedule

betty_busy = convert_schedule(betty_busy_str)
megan_busy = convert_schedule(megan_busy_str)

# Betty cannot meet on Wednesday or Thursday.
# Also Megan is fully busy on Monday and Friday.
# So the only possible day from Monday-Friday is Tuesday.
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

proposed_day = None
proposed_start = None
proposed_end = None

for day in days:
    # Skip days that Betty cannot do
    if day in ["Wednesday", "Thursday"]:
        continue
    # For Megan, if she is busy all day, skip
    if day in megan_busy and len(megan_busy[day]) == 1:
        b_start, b_end = megan_busy[day][0]
        if b_start <= WORK_START and b_end >= WORK_END:
            continue

    # Get busy intervals for Betty and Megan for the day.
    betty_day_busy = betty_busy.get(day, [])
    megan_day_busy = megan_busy.get(day, [])
    
    # Calculate their free intervals within working hours.
    betty_free = get_free_intervals(betty_day_busy, WORK_START, WORK_END)
    megan_free = get_free_intervals(megan_day_busy, WORK_START, WORK_END)
    
    # Find overlapping free times.
    overlaps = intersect_intervals(betty_free, megan_free)
    # Check for an overlap that can fit the meeting duration.
    for start, end in overlaps:
        if end - start >= MEETING_DURATION:
            proposed_day = day
            proposed_start = start
            proposed_end = start + MEETING_DURATION
            break
    if proposed_day:
        break

# Format the meeting time as HH:MM:HH:MM and output with the day.
if proposed_day:
    time_range = f"{minutes_to_time(proposed_start)}:{minutes_to_time(proposed_end)}"
    print(proposed_day)
    print(time_range)
else:
    print("No suitable meeting time found.")