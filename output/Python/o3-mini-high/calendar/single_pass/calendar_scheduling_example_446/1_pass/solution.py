def time_to_minutes(t):
    """Convert time in HH:MM format to minutes since midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to HH:MM format."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Define working hours and meeting duration
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30

# Define each participant's busy intervals on Monday in HH:MM format
busy_schedules = {
    "Megan": [("09:00", "09:30"), ("10:00", "11:00"), ("12:00", "12:30")],
    "Christine": [("09:00", "09:30"), ("11:30", "12:00"), ("13:00", "14:00"), ("15:30", "16:30")],
    "Gabriel": [],  # free the entire day
    "Sara": [("11:30", "12:00"), ("14:30", "15:00")],
    "Bruce": [("09:30", "10:00"), ("10:30", "12:00"), ("12:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:30")],
    "Kathryn": [("10:00", "15:30"), ("16:00", "16:30")],
    "Billy": [("09:00", "09:30"), ("11:00", "11:30"), ("12:00", "14:00"), ("14:30", "15:30")]
}

# Convert all busy intervals to minutes
for person, intervals in busy_schedules.items():
    busy_schedules[person] = [(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals]

def is_free(candidate_start, candidate_end, intervals):
    """
    Check if the candidate interval [candidate_start, candidate_end) 
    does not overlap with any busy interval.
    """
    for busy_start, busy_end in intervals:
        # Overlap occurs if candidate_start < busy_end and busy_start < candidate_end.
        if candidate_start < busy_end and busy_start < candidate_end:
            return False
    return True

# Find a possible meeting time where all participants are free
meeting_time = None
# Iterate over each minute of work hours where a meeting could start
for candidate in range(work_start, work_end - meeting_duration + 1):
    candidate_end = candidate + meeting_duration
    valid = True
    for person, intervals in busy_schedules.items():
        if not is_free(candidate, candidate_end, intervals):
            valid = False
            break
    if valid:
        meeting_time = (candidate, candidate_end)
        break

# Output the result in the required format
if meeting_time:
    start_str = minutes_to_time(meeting_time[0])
    end_str = minutes_to_time(meeting_time[1])
    # Output the day of the week and the time range in HH:MM:HH:MM format.
    print("Monday")
    print(f"{start_str}:{end_str}")
else:
    print("No available meeting time found.")