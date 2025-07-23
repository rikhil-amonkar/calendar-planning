def find_meeting_time(participants_schedules, duration, work_hours, day, preferences=None):
    """
    Finds a suitable meeting time for all participants based on their schedules and preferences.
    
    Args:
        participants_schedules (dict): Dictionary with participant names as keys and their busy times as values.
        duration (int): Duration of the meeting in minutes.
        work_hours (tuple): Tuple of (start_hour, end_hour) in 24-hour format.
        day (str): Day of the week for the meeting.
        preferences (dict): Optional dictionary with participant preferences.
    
    Returns:
        tuple: (start_time, end_time) in HH:MM format, or None if no suitable time is found.
    """
    # Convert work hours to minutes since midnight for easier calculation
    work_start = work_hours[0] * 60
    work_end = work_hours[1] * 60
    
    # Initialize all possible time slots within work hours
    time_slots = []
    current_time = work_start
    while current_time + duration <= work_end:
        time_slots.append((current_time, current_time + duration))
        current_time += 30  # Check in 30-minute increments
    
    # Apply Roger's preference (not before 12:30)
    if preferences and 'Roger' in preferences and 'not_before' in preferences['Roger']:
        not_before_time = preferences['Roger']['not_before'] * 60
        time_slots = [slot for slot in time_slots if slot[0] >= not_before_time]
    
    # Check each time slot against all participants' schedules
    for slot in time_slots:
        slot_start, slot_end = slot
        all_available = True
        
        for participant, busy_times in participants_schedules.items():
            # Check if participant is busy during the slot
            for busy_start, busy_end in busy_times:
                busy_start_min = busy_start[0] * 60 + busy_start[1]
                busy_end_min = busy_end[0] * 60 + busy_end[1]
                
                # Check for overlap
                if not (slot_end <= busy_start_min or slot_start >= busy_end_min):
                    all_available = False
                    break
            
            if not all_available:
                break
        
        if all_available:
            # Convert slot back to HH:MM format
            start_hh = slot_start // 60
            start_mm = slot_start % 60
            end_hh = slot_end // 60
            end_mm = slot_end % 60
            return (f"{start_hh:02d}:{start_mm:02d}", f"{end_hh:02d}:{end_mm:02d}")
    
    return None

# Define participants' schedules
participants_schedules = {
    'Daniel': [],
    'Kathleen': [((14, 30), (15, 30))],
    'Carolyn': [((12, 00), (12, 30)), ((13, 00), (13, 30))],
    'Roger': [],
    'Cheryl': [((9, 00), (9, 30)), ((10, 00), (11, 30)), ((12, 30), (13, 30)), ((14, 00), (17, 00))],
    'Virginia': [((9, 30), (11, 30)), ((12, 00), (12, 30)), ((13, 00), (13, 30)), ((14, 30), (15, 30)), ((16, 00), (17, 00))],
    'Angela': [((9, 30), (10, 00)), ((10, 30), (11, 30)), ((12, 00), (12, 30)), ((13, 00), (13, 30)), ((14, 00), (16, 30))]
}

# Define meeting parameters
duration = 30  # minutes
work_hours = (9, 17)  # 9:00 to 17:00
day = "Monday"
preferences = {'Roger': {'not_before': 12.5}}  # 12:30 in decimal hours

# Find meeting time
meeting_time = find_meeting_time(participants_schedules, duration, work_hours, day, preferences)

if meeting_time:
    start_time, end_time = meeting_time
    print(f"{day}: {start_time}:{end_time}")
else:
    print("No suitable time found.")