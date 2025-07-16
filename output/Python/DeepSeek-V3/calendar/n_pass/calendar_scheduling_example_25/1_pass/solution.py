def find_meeting_time(participants_schedules, work_hours, duration, preferences=None):
    """
    Find a meeting time that fits all participants' schedules and constraints.
    
    Args:
        participants_schedules: Dict of participant names to their busy times in HH:MM format.
        work_hours: Tuple of (start, end) in HH:MM format.
        duration: Duration of the meeting in minutes.
        preferences: Optional constraints (e.g., no meetings after a certain time).
    
    Returns:
        Tuple of (day, start_time, end_time) or None if no slot found.
    """
    # Convert all times to minutes since midnight for easier calculations
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start, work_end = map(time_to_minutes, work_hours)
    duration_min = duration
    
    # Collect all busy intervals for all participants
    all_busy = []
    for participant, schedules in participants_schedules.items():
        for busy in schedules:
            start, end = map(time_to_minutes, busy.split(' to '))
            all_busy.append((start, end))
    
    # Add preference constraints (e.g., Pamela doesn't want to meet after 14:30)
    if preferences:
        for participant, constraint in preferences.items():
            if "after" in constraint:
                time_limit = time_to_minutes(constraint.split("after ")[1])
                all_busy.append((time_limit, work_end))
    
    # Sort all busy intervals by start time
    all_busy.sort()
    
    # Find available slots by merging busy intervals
    merged_busy = []
    for start, end in all_busy:
        if not merged_busy:
            merged_busy.append((start, end))
        else:
            last_start, last_end = merged_busy[-1]
            if start <= last_end:
                # Overlapping or adjacent intervals, merge them
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged_busy[-1] = (new_start, new_end)
            else:
                merged_busy.append((start, end))
    
    # Now find gaps between merged busy intervals that can fit the meeting
    available_slots = []
    prev_end = work_start
    for start, end in merged_busy:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))
    
    # Check each available slot for duration
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration_min:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_min
            return (
                "Monday",
                minutes_to_time(meeting_start),
                minutes_to_time(meeting_end)
            )
    
    return None

# Define participants' schedules
participants_schedules = {
    "Anthony": [
        "09:30 to 10:00",
        "12:00 to 13:00",
        "16:00 to 16:30"
    ],
    "Pamela": [
        "09:30 to 10:00",
        "16:30 to 17:00"
    ],
    "Zachary": [
        "09:00 to 11:30",
        "12:00 to 12:30",
        "13:00 to 13:30",
        "14:30 to 15:00",
        "16:00 to 17:00"
    ]
}

# Define preferences
preferences = {
    "Pamela": "do not want to meet after 14:30"
}

# Define work hours and duration
work_hours = ("09:00", "17:00")
duration_minutes = 60  # 1 hour

# Find meeting time
result = find_meeting_time(participants_schedules, work_hours, duration_minutes, preferences)
if result:
    day, start_time, end_time = result
    print(f"{day}: {start_time}:{end_time}")
else:
    print("No suitable time found.")