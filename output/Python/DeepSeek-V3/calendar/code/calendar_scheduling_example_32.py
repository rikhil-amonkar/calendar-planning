def find_meeting_time(participants_schedules, duration, work_hours, day, preferences=None):
    """
    Finds a meeting time that fits all participants' schedules and constraints.
    
    Args:
        participants_schedules: List of lists of busy time ranges for each participant.
        duration: Duration of the meeting in minutes.
        work_hours: Tuple of (start_hour, end_hour) in 24-hour format.
        day: Day of the week.
        preferences: Optional constraints (e.g., no meetings after a certain time).
    
    Returns:
        A tuple of (start_time, end_time) in HH:MM format, or None if no time found.
    """
    # Convert all times to minutes since midnight for easier calculation
    work_start = work_hours[0] * 60
    work_end = work_hours[1] * 60
    
    # Generate all possible time slots within work hours
    slots = []
    current_time = work_start
    while current_time + duration <= work_end:
        slots.append((current_time, current_time + duration))
        current_time += 15  # Check in 15-minute increments
    
    # Apply Frank's preference: no meetings after 9:30 (570 minutes)
    if preferences and "no_meeting_after" in preferences:
        no_meeting_after = preferences["no_meeting_after"] * 60
        slots = [slot for slot in slots if slot[0] < no_meeting_after]
    
    # Check each slot against all participants' schedules
    for slot in slots:
        slot_start, slot_end = slot
        valid = True
        
        for schedule in participants_schedules:
            for busy_start, busy_end in schedule:
                busy_start_min = busy_start[0] * 60 + busy_start[1]
                busy_end_min = busy_end[0] * 60 + busy_end[1]
                
                # Check if slot overlaps with any busy time
                if not (slot_end <= busy_start_min or slot_start >= busy_end_min):
                    valid = False
                    break
            
            if not valid:
                break
        
        if valid:
            # Convert back to HH:MM format
            start_hh = slot_start // 60
            start_mm = slot_start % 60
            end_hh = slot_end // 60
            end_mm = slot_end % 60
            return (f"{start_hh:02d}:{start_mm:02d}", f"{end_hh:02d}:{end_mm:02d}")
    
    return None

# Define participants' schedules in (HH, MM) format
emily_schedule = [
    ((10, 0), (10, 30)),
    ((11, 30), (12, 30)),
    ((14, 0), (15, 0)),
    ((16, 0), (16, 30))
]

melissa_schedule = [
    ((9, 30), (10, 0)),
    ((14, 30), (15, 0))
]

frank_schedule = [
    ((10, 0), (10, 30)),
    ((11, 0), (11, 30)),
    ((12, 30), (13, 0)),
    ((13, 30), (14, 30)),
    ((15, 0), (16, 0)),
    ((16, 30), (17, 0))
]

participants_schedules = [emily_schedule, melissa_schedule, frank_schedule]
duration = 30  # minutes
work_hours = (9, 17)  # 9:00 to 17:00
day = "Monday"
preferences = {"no_meeting_after": 9.5}  # 9:30

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, duration, work_hours, day, preferences)

if meeting_time:
    start_time, end_time = meeting_time
    print(f"{day}: {start_time}:{end_time}")
else:
    print("No suitable time found.")