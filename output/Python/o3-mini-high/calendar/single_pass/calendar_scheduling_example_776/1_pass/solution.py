def time_to_minutes(time_str):
    """Convert a HH:MM string into minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to a HH:MM string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    """
    Given a list of busy intervals (as tuples of (start, end) in minutes) and working hours,
    return a list of free intervals within the working period.
    """
    free = []
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

# Meeting duration is 30 minutes.
meeting_duration = 30

# Jennifer's working hours are 09:00 to 17:00.
jennifer_work_start = time_to_minutes("09:00")
jennifer_work_end = time_to_minutes("17:00")

# Jennifer's busy schedule for each day (in minutes).
busy_schedules = {
    "Monday": [
        (time_to_minutes("09:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("17:00"))
    ],
    "Tuesday": [
        (time_to_minutes("09:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("17:00"))
    ],
    "Wednesday": [
        (time_to_minutes("09:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

def get_john_working_hours(day):
    """
    John's overall work day is 09:00 to 17:00,
    but he prefers not to have additional meetings on Monday after 14:30.
    """
    if day == "Monday":
        return time_to_minutes("09:00"), time_to_minutes("14:30")
    else:
        return time_to_minutes("09:00"), time_to_minutes("17:00")

# Candidate days in order.
days = ["Monday", "Tuesday", "Wednesday"]

meeting_day = None
meeting_start = None

for day in days:
    # Get John's available period for the day.
    john_start, john_end = get_john_working_hours(day)
    
    # Compute Jennifer's free intervals (based on her work hours).
    jennifer_free = get_free_intervals(
        busy_schedules[day],
        jennifer_work_start,
        jennifer_work_end
    )
    
    # Look for a free slot that both can attend.
    for free_start, free_end in jennifer_free:
        # The available slot is the intersection of Jennifer's free interval and John's working period.
        slot_start = max(free_start, john_start)
        slot_end = min(free_end, john_end)
        if slot_end - slot_start >= meeting_duration:
            meeting_day = day
            meeting_start = slot_start
            break
    if meeting_day is not None:
        break

if meeting_day is not None:
    meeting_end = meeting_start + meeting_duration
    # Format times into HH:MM strings.
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    # Output: time range in the format HH:MM:HH:MM and the day of the week.
    print(f"{start_str}:{end_str}")
    print(meeting_day)
else:
    print("No available meeting slot found.")