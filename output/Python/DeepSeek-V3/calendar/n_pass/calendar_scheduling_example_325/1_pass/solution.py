def find_meeting_time(participants_schedules, duration, work_hours_start, work_hours_end, day, constraints=None):
    """
    Find a meeting time that fits all participants' schedules and constraints.
    
    Args:
        participants_schedules (dict): Dictionary with participant names as keys and list of busy time slots as values.
        duration (int): Duration of the meeting in minutes.
        work_hours_start (str): Start of work hours in 'HH:MM' format.
        work_hours_end (str): End of work hours in 'HH:MM' format.
        day (str): Day of the week for the meeting.
        constraints (dict, optional): Additional constraints like 'not after' time. Defaults to None.
    
    Returns:
        tuple: (start_time, end_time) in 'HH:MM' format, or None if no slot found.
    """
    # Convert work hours to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    
    # Convert all busy slots to minutes
    busy_slots = []
    for participant, slots in participants_schedules.items():
        for slot in slots:
            start, end = map(time_to_minutes, slot.split(' to '))
            busy_slots.append((start, end))
    
    # Add constraints (e.g., Jose doesn't want to meet after 15:30)
    if constraints:
        for name, constraint in constraints.items():
            if name in participants_schedules:
                constraint_time = time_to_minutes(constraint['not_after'])
                # Add a busy slot from constraint_time to work_end for the participant
                busy_slots.append((constraint_time, work_end))
    
    # Sort all busy slots by start time
    busy_slots.sort()
    
    # Find free slots by merging busy slots and checking gaps
    free_slots = []
    prev_end = work_start
    
    for start, end in busy_slots:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    # Check the last slot after all busy slots
    if prev_end < work_end:
        free_slots.append((prev_end, work_end))
    
    # Find the first free slot that can fit the meeting duration
    duration_minutes = duration * 60  # Convert hours to minutes (assuming duration is in hours)
    for start, end in free_slots:
        if end - start >= duration_minutes:
            # Convert back to 'HH:MM' format
            def minutes_to_time(minutes):
                hh = minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"
            
            meeting_start = minutes_to_time(start)
            meeting_end = minutes_to_time(start + duration_minutes)
            return (meeting_start, meeting_end)
    
    return None

# Define participants' schedules
participants_schedules = {
    'Jose': ['11:00 to 11:30', '12:30 to 13:00'],
    'Keith': ['14:00 to 14:30', '15:00 to 15:30'],
    'Logan': ['09:00 to 10:00', '12:00 to 12:30', '15:00 to 15:30'],
    'Megan': ['09:00 to 10:30', '11:00 to 12:00', '13:00 to 13:30', '14:30 to 16:30'],
    'Gary': ['09:00 to 09:30', '10:00 to 10:30', '11:30 to 13:00', '13:30 to 14:00', '14:30 to 16:30'],
    'Bobby': ['11:00 to 11:30', '12:00 to 12:30', '13:00 to 16:00']
}

# Define constraints
constraints = {
    'Jose': {'not_after': '15:30'}
}

# Find meeting time
meeting_time = find_meeting_time(
    participants_schedules,
    duration=0.5,  # 30 minutes
    work_hours_start='09:00',
    work_hours_end='17:00',
    day='Monday',
    constraints=constraints
)

if meeting_time:
    start, end = meeting_time
    print(f"{{{start}:{end}}} {day}")
else:
    print("No suitable time found.")