def time_to_minutes(time_str):
    """Convert HH:MM string to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to HH:MM format."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define working hours on Monday
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30

# Define busy intervals for each participant (in minutes)
schedules = {
    "Andrea": [],  # Fully available
    "Jack": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("14:00"), time_to_minutes("14:30"))
    ],
    "Madison": [
        (time_to_minutes("09:30"), time_to_minutes("10:30")),
        (time_to_minutes("13:00"), time_to_minutes("14:00")),
        (time_to_minutes("15:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    "Rachel": [
        (time_to_minutes("09:30"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ],
    "Douglas": [
        (time_to_minutes("09:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("16:30"))
    ],
    "Ryan": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("13:00"), time_to_minutes("14:00")),
        (time_to_minutes("14:30"), time_to_minutes("17:00"))
    ]
}

def is_time_slot_free(start, duration, schedules):
    """Check if all participants are free for the duration starting at 'start'."""
    end = start + duration
    # Ensure the meeting fits within working hours
    if start < work_start or end > work_end:
        return False

    # Check each participant's busy intervals for overlap.
    for person, busy_intervals in schedules.items():
        for busy_start, busy_end in busy_intervals:
            # Overlap exists if: start < busy_end and end > busy_start
            if start < busy_end and end > busy_start:
                return False
    return True

# Find a common 30-minute slot
meeting_start_time = None
for t in range(work_start, work_end - meeting_duration + 1):
    if is_time_slot_free(t, meeting_duration, schedules):
        meeting_start_time = t
        break

if meeting_start_time is not None:
    meeting_end_time = meeting_start_time + meeting_duration
    meeting_start_str = minutes_to_time(meeting_start_time)
    meeting_end_str = minutes_to_time(meeting_end_time)
    # Output in the required format: Day, HH:MM:HH:MM
    print(f"Monday, {meeting_start_str}:{meeting_end_str}")
else:
    print("No valid meeting time found.")