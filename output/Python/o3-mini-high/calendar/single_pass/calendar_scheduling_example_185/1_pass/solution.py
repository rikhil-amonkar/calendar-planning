def time_to_minutes(time_str):
    """Converts 'HH:MM' into minutes from midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Converts minutes from midnight into 'HH:MM' format."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define work hours and meeting duration (in minutes)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30

# Megan prefers not to have meetings before 10:00.
earliest_start = max(work_start, time_to_minutes("10:00"))
latest_start = work_end - meeting_duration

# Busy schedules for each person, formatted as (start, end) in minutes.
busy = {
    "Kimberly": [
        (time_to_minutes("10:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("12:00")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ],
    "Megan": [
        # Megan has no meetings.
    ],
    "Marie": [
        (time_to_minutes("10:00"), time_to_minutes("11:00")),
        (time_to_minutes("11:30"), time_to_minutes("15:00")),
        (time_to_minutes("16:00"), time_to_minutes("16:30"))
    ],
    "Diana": [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:30"), time_to_minutes("17:00"))
    ]
}

def is_slot_free(candidate_start):
    """Checks if a meeting starting at candidate_start for meeting_duration is free for all."""
    candidate_end = candidate_start + meeting_duration
    # Ensure the meeting is within work hours.
    if candidate_start < work_start or candidate_end > work_end:
        return False
    # Check each person's busy intervals.
    for person in busy:
        for b_start, b_end in busy[person]:
            # Overlap occurs if candidate_start < b_end and b_start < candidate_end.
            if candidate_start < b_end and b_start < candidate_end:
                return False
    return True

# Find the first available slot that works for everyone.
meeting_start = None
for candidate in range(earliest_start, latest_start + 1):
    if is_slot_free(candidate):
        meeting_start = candidate
        break

if meeting_start is not None:
    meeting_day = "Monday"
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_start + meeting_duration)
    # Output in the format "Day HH:MM:HH:MM"
    print(f"{meeting_day} {start_str}:{end_str}")
else:
    print("No available slot found.")