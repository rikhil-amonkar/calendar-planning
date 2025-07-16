def find_meeting_time(participants_schedules, work_hours, duration, preferences=None):
    """
    Finds a suitable meeting time for all participants based on their schedules and constraints.
    
    Args:
        participants_schedules (dict): Dictionary with participant names as keys and their blocked times as values.
        work_hours (tuple): Tuple of (start_hour, end_hour) in 24-hour format.
        duration (int): Duration of the meeting in minutes.
        preferences (dict, optional): Dictionary of preferences (e.g., 'no_after' time).
    
    Returns:
        dict: {'day': str, 'time_range': str} or None if no time found.
    """
    day = "Monday"  # As per the task, the day is fixed
    
    # Convert work hours to minutes since midnight for easier calculation
    work_start = work_hours[0] * 60
    work_end = work_hours[1] * 60
    
    # Generate all possible time slots within work hours
    time_slots = []
    current_time = work_start
    while current_time + duration <= work_end:
        time_slots.append((current_time, current_time + duration))
        current_time += 15  # Check every 15 minutes for granularity
    
    # Check each time slot against all participants' schedules and preferences
    for slot_start, slot_end in time_slots:
        slot_valid = True
        
        # Check against each participant's schedule
        for participant, blocked_times in participants_schedules.items():
            for block_start, block_end in blocked_times:
                block_start_min = block_start[0] * 60 + block_start[1]
                block_end_min = block_end[0] * 60 + block_end[1]
                
                # Check if slot overlaps with any blocked time
                if not (slot_end <= block_start_min or slot_start >= block_end_min):
                    slot_valid = False
                    break
            if not slot_valid:
                break
        
        # Check preferences if slot is still valid
        if slot_valid and preferences:
            for participant, pref in preferences.items():
                if 'no_after' in pref:
                    no_after_min = pref['no_after'][0] * 60 + pref['no_after'][1]
                    if slot_start >= no_after_min:
                        slot_valid = False
                        break
            if not slot_valid:
                continue
        
        if slot_valid:
            # Convert slot back to HH:MM format
            start_hh = slot_start // 60
            start_mm = slot_start % 60
            end_hh = slot_end // 60
            end_mm = slot_end % 60
            time_range = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
            return {'day': day, 'time_range': time_range}
    
    return None

# Define participants' schedules in HH:MM format
margaret_schedule = [
    ((9, 0), (10, 0)),
    ((10, 30), (11, 0)),
    ((11, 30), (12, 0)),
    ((13, 0), (13, 30)),
    ((15, 0), (15, 30))
]

donna_schedule = [
    ((14, 30), (15, 0)),
    ((16, 0), (16, 30))
]

helen_schedule = [
    ((9, 0), (9, 30)),
    ((10, 0), (11, 30)),
    ((13, 0), (14, 0)),
    ((14, 30), (15, 0)),
    ((15, 30), (17, 0))
]

# Combine all schedules
participants_schedules = {
    'Margaret': margaret_schedule,
    'Donna': donna_schedule,
    'Helen': helen_schedule
}

# Define work hours (9:00 to 17:00)
work_hours = (9, 17)

# Meeting duration in minutes (30 minutes)
duration = 30

# Define Helen's preference (no meetings after 13:30)
preferences = {
    'Helen': {'no_after': (13, 30)}
}

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, work_hours, duration, preferences)

# Output the result
if meeting_time:
    print(f"{meeting_time['time_range']} on {meeting_time['day']}")
else:
    print("No suitable time found.")