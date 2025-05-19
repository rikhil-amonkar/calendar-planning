def time_to_minutes(time_str):
    """Convert HH:MM time string to minutes from midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes from midnight to HH:MM time string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Meeting duration in minutes
meeting_duration = 30

# Define the working day hours
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Busy schedules for the participants on Monday (in minutes)
busy_jack = [
    (time_to_minutes("09:30"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

busy_charlotte = [
    (time_to_minutes("09:30"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("16:00"))
]

# Jack prefers to avoid meetings after 12:30 on Monday,
# so we want the meeting to finish by 12:30.
# We'll enforce that the meeting must end by or before 12:30.
jack_preference_limit = time_to_minutes("12:30")

def is_free(busy_list, start, end):
    """Check if the person is free between start and end (in minutes)."""
    for busy_start, busy_end in busy_list:
        # If the meeting overlaps with any busy interval, return False.
        if start < busy_end and end > busy_start:
            return False
    return True

# Try to find an available time slot that satisfies all constraints.
available_slot = None
# We only consider start times where the meeting will finish by work_end.
for start in range(work_start, work_end - meeting_duration + 1):
    end = start + meeting_duration

    # Enforce Jack's preference: the meeting must finish by 12:30.
    if end > jack_preference_limit:
        continue

    # Check if both Jack and Charlotte are free during this interval.
    if is_free(busy_jack, start, end) and is_free(busy_charlotte, start, end):
        available_slot = (start, end)
        break

if available_slot:
    meeting_start, meeting_end = available_slot
    # Output in the format {HH:MM:HH:MM} and include the day of the week.
    print("Monday", f"{{{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}}}")
else:
    print("No available time slot found.")