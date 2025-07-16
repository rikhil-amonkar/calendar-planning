def find_meeting_time(participants_schedules, day, work_start, work_end, duration):
    """
    Finds a meeting time that fits all participants' schedules.
    
    Args:
        participants_schedules (dict): A dictionary where keys are participant names and values are lists of busy time slots in HH:MM format.
        day (str): The day of the week for the meeting.
        work_start (str): Start of work hours in HH:MM format.
        work_end (str): End of work hours in HH:MM format.
        duration (int): Duration of the meeting in minutes.
    
    Returns:
        tuple: (day, start_time, end_time) if a slot is found, otherwise (None, None, None).
    """
    # Convert all time strings to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    duration_min = duration
    
    # Collect all busy slots from all participants
    all_busy_slots = []
    for busy_slots in participants_schedules.values():
        for slot in busy_slots:
            start, end = map(time_to_minutes, slot.split(':'))
            all_busy_slots.append((start, end))
    
    # Sort all busy slots by start time
    all_busy_slots.sort()
    
    # Find available slots by merging busy slots
    available_slots = []
    prev_end = work_start_min
    
    for start, end in all_busy_slots:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end_min:
        available_slots.append((prev_end, work_end_min))
    
    # Check each available slot for duration
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration_min:
            # Convert back to HH:MM format
            def minutes_to_time(minutes):
                hh = minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"
            
            meeting_start = minutes_to_time(slot_start)
            meeting_end = minutes_to_time(slot_start + duration_min)
            return (day, meeting_start, meeting_end)
    
    return (None, None, None)

# Define participants' schedules
participants_schedules = {
    "Tyler": [],
    "Kelly": [],
    "Stephanie": ["11:00:11:30", "14:30:15:00"],
    "Hannah": [],
    "Joe": ["09:00:09:30", "10:00:12:00", "12:30:13:00", "14:00:17:00"],
    "Diana": ["09:00:10:30", "11:30:12:00", "13:00:14:00", "14:30:15:30", "16:00:17:00"],
    "Deborah": ["09:00:10:00", "10:30:12:00", "12:30:13:00", "13:30:14:00", "14:30:15:30", "16:00:16:30"]
}

# Find meeting time
day = "Monday"
work_start = "09:00"
work_end = "17:00"
duration = 30  # minutes

day, start_time, end_time = find_meeting_time(participants_schedules, day, work_start, work_end, duration)

# Output the result
if start_time and end_time:
    print(f"{day}: {start_time}:{end_time}")
else:
    print("No suitable time found.")