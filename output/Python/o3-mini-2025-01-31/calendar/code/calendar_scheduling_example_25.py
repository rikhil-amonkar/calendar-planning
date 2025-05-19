def time_to_minutes(time_str):
    """Converts a time string HH:MM into total minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Converts minutes since midnight into a time string HH:MM."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define the meeting duration in minutes
meeting_duration = 60

# Define working hours (in minutes)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Pamela's constraint: meeting must finish by 14:30
pamelas_latest_end = time_to_minutes("14:30")
# So meeting must start no later than:
latest_start = min(work_end - meeting_duration, pamelas_latest_end - meeting_duration)

# Busy intervals for each participant are defined as (start, end) in minutes
busy_intervals = {
    "Anthony": [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("12:00"), time_to_minutes("13:00")),
        (time_to_minutes("16:00"), time_to_minutes("16:30")),
    ],
    "Pamela": [
        (time_to_minutes("09:30"), time_to_minutes("10:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    "Zachary": [
        (time_to_minutes("09:00"), time_to_minutes("11:30")),
        (time_to_minutes("12:00"), time_to_minutes("12:30")),
        (time_to_minutes("13:00"), time_to_minutes("13:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ]
}

def has_conflict(start, end, intervals):
    for interval_start, interval_end in intervals:
        # Check if [start, end) overlaps with [interval_start, interval_end)
        if start < interval_end and interval_start < end:
            return True
    return False

# Function to check if a candidate meeting time is free for all participants
def is_time_slot_free(candidate_start):
    candidate_end = candidate_start + meeting_duration
    # Check that meeting fits in working hours and meets Pamela's constraint
    if candidate_start < work_start or candidate_end > work_end:
        return False
    if candidate_end > pamelas_latest_end:
        return False
    # Check each participant's busy intervals for conflict
    for person, intervals in busy_intervals.items():
        if has_conflict(candidate_start, candidate_end, intervals):
            return False
    return True

# Find the first candidate time that works from work_start up to latest_start (inclusive)
meeting_time = None
for start in range(work_start, latest_start + 1):
    if is_time_slot_free(start):
        meeting_time = (start, start + meeting_duration)
        break

if meeting_time:
    start_str = minutes_to_time(meeting_time[0])
    end_str = minutes_to_time(meeting_time[1])
    # Output in the format HH:MM:HH:MM and the day Monday
    print(f"{start_str}:{end_str} Monday")
else:
    print("No available meeting time found on Monday.")