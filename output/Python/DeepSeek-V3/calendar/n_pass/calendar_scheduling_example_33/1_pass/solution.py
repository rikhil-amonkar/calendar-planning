def find_meeting_time(participants_schedules, duration, work_hours, preferences=None):
    """
    Find a suitable meeting time for all participants considering their schedules and preferences.
    
    Args:
        participants_schedules (dict): Dictionary with participant names as keys and their busy times as values.
        duration (int): Duration of the meeting in minutes.
        work_hours (tuple): Tuple of (start_hour, end_hour) in 24-hour format.
        preferences (dict, optional): Dictionary with participant preferences. Defaults to None.
    
    Returns:
        tuple: (day, start_time, end_time) if a slot is found, else (None, None, None).
    """
    # Convert work hours to minutes since midnight for easier calculation
    work_start = work_hours[0] * 60
    work_end = work_hours[1] * 60
    
    # Generate all possible time slots within work hours
    time_slots = []
    current_time = work_start
    while current_time + duration <= work_end:
        time_slots.append((current_time, current_time + duration))
        current_time += 30  # Assuming 30-minute increments for simplicity
    
    # Check each time slot against all participants' schedules
    for slot in time_slots:
        slot_start, slot_end = slot
        valid = True
        
        for participant, busy_times in participants_schedules.items():
            # Check if the participant is busy during the slot
            for busy_start, busy_end in busy_times:
                busy_start_min = busy_start[0] * 60 + busy_start[1]
                busy_end_min = busy_end[0] * 60 + busy_end[1]
                if not (slot_end <= busy_start_min or slot_start >= busy_end_min):
                    valid = False
                    break
            
            # Check preferences if any
            if valid and preferences and participant in preferences:
                pref = preferences[participant]
                if 'avoid_after' in pref:
                    avoid_after_min = pref['avoid_after'][0] * 60 + pref['avoid_after'][1]
                    if slot_start >= avoid_after_min:
                        valid = False
            
            if not valid:
                break
        
        if valid:
            # Convert slot back to HH:MM format
            start_hh = slot_start // 60
            start_mm = slot_start % 60
            end_hh = slot_end // 60
            end_mm = slot_end % 60
            return ("Monday", 
                    f"{start_hh:02d}:{start_mm:02d}", 
                    f"{end_hh:02d}:{end_mm:02d}")
    
    return (None, None, None)

# Define participants' schedules in (HH, MM) format
participants_schedules = {
    "Lisa": [
        ((9, 0), (10, 0)),
        ((10, 30), (11, 30)),
        ((12, 30), (13, 0)),
        ((16, 0), (16, 30))
    ],
    "Bobby": [
        ((9, 0), (9, 30)),
        ((10, 0), (10, 30)),
        ((11, 30), (12, 0)),
        ((15, 0), (15, 30))
    ],
    "Randy": [
        ((9, 30), (10, 0)),
        ((10, 30), (11, 0)),
        ((11, 30), (12, 30)),
        ((13, 0), (13, 30)),
        ((14, 30), (15, 30)),
        ((16, 0), (16, 30))
    ]
}

# Define preferences
preferences = {
    "Bobby": {
        "avoid_after": (15, 0)  # Avoid after 15:00
    }
}

# Define work hours (9:00 to 17:00)
work_hours = (9, 17)

# Meeting duration in minutes
duration = 30

# Find the meeting time
day, start_time, end_time = find_meeting_time(participants_schedules, duration, work_hours, preferences)

if day:
    print(f"{day}:{{{start_time}:{end_time}}}")
else:
    print("No suitable time found.")