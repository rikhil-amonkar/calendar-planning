def time_to_minutes(time_str):
    """Converts HH:MM string to minutes past midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Converts minutes past midnight to HH:MM string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Meeting details and constraints
meeting_day = "Monday"
meeting_duration = 30  # in minutes

# General working hours for Monday: 09:00 to 17:00
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Evelyn's availability:
# Evelyn has no meetings but does NOT want to meet after 13:00.
# Therefore, her available window is 09:00 to 13:00.
evelyn_avail_start = work_start
evelyn_avail_end = time_to_minutes("13:00")

# Randy's busy intervals on Monday:
# Blocked times: 09:00-10:30, 11:00-15:30, 16:00-17:00
randy_busy = [
    (time_to_minutes("09:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

def get_free_intervals(start, end, busy_intervals):
    """Given working hours and busy intervals, returns free intervals."""
    free = []
    current = start
    for busy_start, busy_end in busy_intervals:
        if busy_start > current:
            free.append((current, busy_start))
        current = max(current, busy_end)
    if current < end:
        free.append((current, end))
    return free

# Get Randy's free intervals within the working hours.
randy_free = get_free_intervals(work_start, work_end, randy_busy)

# Find a common free slot that satisfies both Evelyn and Randy.
# We need to intersect Randy's free intervals with Evelyn's availability.
common_slot = None
for free_start, free_end in randy_free:
    # Adjust for Evelyn's constraint
    available_start = max(free_start, evelyn_avail_start)
    available_end = min(free_end, evelyn_avail_end)
    # Check if the available interval is long enough for the meeting.
    if available_end - available_start >= meeting_duration:
        common_slot = (available_start, available_start + meeting_duration)
        break

if common_slot:
    start_minutes, end_minutes = common_slot
    meeting_time = f"{minutes_to_time(start_minutes)}:{minutes_to_time(end_minutes)}"
    print(f"{meeting_day}, {meeting_time}")
else:
    print("No available meeting slot found.")