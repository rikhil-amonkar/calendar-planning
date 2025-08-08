def time_to_minutes(t_str):
    hours, minutes = map(int, t_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Busy schedules for each participant (start, end) in HH:MM format.
schedules = {
    "Patrick": [("09:00", "09:30"), ("10:00", "10:30"), ("13:30", "14:00"), ("16:00", "16:30")],
    "Kayla":    [("12:30", "13:30"), ("15:00", "15:30"), ("16:00", "16:30")],
    "Carl":     [("10:30", "11:00"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "17:00")],
    "Christian":[("09:00", "12:30"), ("13:00", "14:00"), ("14:30", "17:00")]
}

# Convert all busy intervals to minutes.
for person in schedules:
    schedules[person] = [(time_to_minutes(start), time_to_minutes(end)) 
                           for start, end in schedules[person]]

meeting_duration = 30  # Duration in minutes.
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

def is_slot_free(start, busy_intervals, duration):
    """Check if the meeting slot starting at 'start' and lasting 'duration'
    overlaps with any busy interval."""
    for busy_start, busy_end in busy_intervals:
        if start < busy_end and (start + duration) > busy_start:
            return False
    return True

meeting_time = None

# Iterate over each minute of the working day where a meeting could fit.
for t in range(work_start, work_end - meeting_duration + 1):
    available = True
    for person, busy_intervals in schedules.items():
        if not is_slot_free(t, busy_intervals, meeting_duration):
            available = False
            break
    if available:
        meeting_time = t
        break

if meeting_time is not None:
    start_str = minutes_to_time(meeting_time)
    end_str = minutes_to_time(meeting_time + meeting_duration)
    print(f"Monday {start_str}:{end_str}")
else:
    print("No available meeting time found.")