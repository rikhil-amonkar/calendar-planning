def find_meeting_time(participants_schedules, duration_minutes=30, work_hours_start="09:00", work_hours_end="17:00"):
    """
    Find a meeting time that fits all participants' schedules.
    
    Args:
        participants_schedules (dict): Dictionary with participant names as keys and lists of busy time slots as values.
                                      Each time slot is a tuple of start and end times in "HH:MM" format.
        duration_minutes (int): Duration of the meeting in minutes.
        work_hours_start (str): Start of work hours in "HH:MM" format.
        work_hours_end (str): End of work hours in "HH:MM" format.
    
    Returns:
        tuple: (day, start_time, end_time) if a slot is found, else (None, None, None).
    """
    def time_to_minutes(time_str):
        """Convert HH:MM time string to minutes since midnight."""
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    def minutes_to_time(minutes):
        """Convert minutes since midnight to HH:MM time string."""
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    
    # Collect all busy slots from all participants
    all_busy_slots = []
    for busy_slots in participants_schedules.values():
        for start, end in busy_slots:
            all_busy_slots.append((time_to_minutes(start), time_to_minutes(end)))
    
    # Sort all busy slots by start time
    all_busy_slots.sort()
    
    # Find the earliest available slot
    prev_end = work_start
    for start, end in all_busy_slots:
        if start > prev_end:
            available_duration = start - prev_end
            if available_duration >= duration_minutes:
                return ("Monday", minutes_to_time(prev_end), minutes_to_time(prev_end + duration_minutes))
        prev_end = max(prev_end, end)
    
    # Check after the last busy slot
    if work_end - prev_end >= duration_minutes:
        return ("Monday", minutes_to_time(prev_end), minutes_to_time(prev_end + duration_minutes))
    
    return (None, None, None)

# Define participants' schedules
participants_schedules = {
    "Bradley": [
        ("09:30", "10:00"),
        ("12:30", "13:00"),
        ("13:30", "14:00"),
        ("15:30", "16:00")
    ],
    "Teresa": [
        ("10:30", "11:00"),
        ("12:00", "12:30"),
        ("13:00", "13:30"),
        ("14:30", "15:00")
    ],
    "Elizabeth": [
        ("09:00", "09:30"),
        ("10:30", "11:30"),
        ("13:00", "13:30"),
        ("14:30", "15:00"),
        ("15:30", "17:00")
    ],
    "Christian": [
        ("09:00", "09:30"),
        ("10:30", "17:00")
    ]
}

# Find the meeting time
day, start_time, end_time = find_meeting_time(participants_schedules)

# Output the result
if day:
    print(f"{day}:{start_time}:{end_time}")
else:
    print("No suitable time found.")