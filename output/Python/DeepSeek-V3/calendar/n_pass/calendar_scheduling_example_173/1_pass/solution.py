def find_meeting_time(participants_schedules, duration, work_hours, preferences=None):
    """
    Finds a meeting time that fits all participants' schedules and constraints.
    
    Args:
        participants_schedules: Dict of participant names to their busy times.
        duration: Duration of the meeting in minutes.
        work_hours: Tuple of (start_hour, end_hour) in 24-hour format.
        preferences: Optional dict of preferences (e.g., no meetings after a certain time).
    
    Returns:
        A tuple of (day, start_time, end_time) or None if no time is found.
    """
    day = "Monday"  # Given in the task
    
    # Convert work hours to minutes since midnight
    work_start = work_hours[0] * 60
    work_end = work_hours[1] * 60
    
    # Initialize a list to mark busy times
    time_slots = [True] * (work_end - work_start)  # True means available
    
    # Mark busy times for each participant
    for participant, busy_periods in participants_schedules.items():
        for start, end in busy_periods:
            start_min = start[0] * 60 + start[1]
            end_min = end[0] * 60 + end[1]
            # Adjust to work hours
            start_slot = max(start_min, work_start) - work_start
            end_slot = min(end_min, work_end) - work_start
            for i in range(start_slot, end_slot):
                if i < len(time_slots):
                    time_slots[i] = False
    
    # Apply Harold's preference: no meetings after 13:00
    if preferences and "Harold" in preferences:
        no_meet_after = preferences["Harold"]
        no_meet_after_min = no_meet_after[0] * 60 + no_meet_after[1] - work_start
        for i in range(no_meet_after_min, len(time_slots)):
            time_slots[i] = False
    
    # Find a continuous block of available time slots
    required_slots = duration
    current_start = None
    consecutive_available = 0
    
    for i in range(len(time_slots)):
        if time_slots[i]:
            if current_start is None:
                current_start = i
            consecutive_available += 1
            if consecutive_available >= required_slots:
                # Found a suitable block
                start_min = current_start + work_start
                end_min = start_min + required_slots
                start_time = (start_min // 60, start_min % 60)
                end_time = (end_min // 60, end_min % 60)
                return (day, start_time, end_time)
        else:
            current_start = None
            consecutive_available = 0
    
    return None

# Define participants' schedules in (hour, minute) format
participants_schedules = {
    "Jacqueline": [
        ((9, 0), (9, 30)),
        ((11, 0), (11, 30)),
        ((12, 30), (13, 0)),
        ((15, 30), (16, 0))
    ],
    "Harold": [
        ((10, 0), (10, 30)),
        ((13, 0), (13, 30)),
        ((15, 0), (17, 0))
    ],
    "Arthur": [
        ((9, 0), (9, 30)),
        ((10, 0), (12, 30)),
        ((14, 30), (15, 0)),
        ((15, 30), (17, 0))
    ],
    "Kelly": [
        ((9, 0), (9, 30)),
        ((10, 0), (11, 0)),
        ((11, 30), (12, 30)),
        ((14, 0), (15, 0)),
        ((15, 30), (16, 0))
    ]
}

# Harold's preference: no meetings after 13:00
preferences = {
    "Harold": (13, 0)  # Note: Typo in the original task ("Harold" vs "Harold")
}

# Work hours: 9:00 to 17:00
work_hours = (9, 17)

# Meeting duration: 30 minutes
duration = 30

# Find the meeting time
result = find_meeting_time(participants_schedules, duration, work_hours, preferences)

if result:
    day, start_time, end_time = result
    start_str = f"{start_time[0]:02d}:{start_time[1]:02d}"
    end_str = f"{end_time[0]:02d}:{end_time[1]:02d}"
    print(f"{day}: {start_str}:{end_str}")
else:
    print("No suitable time found.")