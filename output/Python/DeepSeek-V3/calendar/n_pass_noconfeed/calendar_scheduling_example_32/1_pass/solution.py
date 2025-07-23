def find_meeting_time(participants_schedules, duration, work_hours, preferences=None):
    """
    Find a meeting time that fits all participants' schedules and constraints.
    
    Args:
        participants_schedules: Dict of participants with their busy times.
        duration: Duration of the meeting in minutes.
        work_hours: Tuple of (start_hour, end_hour) in 24-hour format.
        preferences: Optional constraints (e.g., no meetings after a certain time).
    
    Returns:
        A tuple (day, time_range) where time_range is in "HH:MM:HH:MM" format.
    """
    day = "Monday"  # Given in the task
    
    # Convert work hours to minutes since midnight
    work_start = work_hours[0] * 60
    work_end = work_hours[1] * 60
    
    # Generate all possible 30-minute slots within work hours
    slots = []
    current = work_start
    while current + duration <= work_end:
        slots.append((current, current + duration))
        current += 30  # Assuming 30-minute granularity
    
    # Filter slots based on Frank's preference (no meetings after 9:30)
    if preferences and "Frank" in preferences:
        no_meeting_after = preferences["Frank"]
        no_meeting_after_min = no_meeting_after[0] * 60 + no_meeting_after[1]
        slots = [slot for slot in slots if slot[0] < no_meeting_after_min]
    
    # Check each slot against participants' busy times
    for slot_start, slot_end in slots:
        slot_ok = True
        for participant, busy_times in participants_schedules.items():
            for busy_start, busy_end in busy_times:
                busy_start_min = busy_start[0] * 60 + busy_start[1]
                busy_end_min = busy_end[0] * 60 + busy_end[1]
                # Check if slot overlaps with busy time
                if not (slot_end <= busy_start_min or slot_start >= busy_end_min):
                    slot_ok = False
                    break
            if not slot_ok:
                break
        if slot_ok:
            # Convert slot back to HH:MM format
            start_hh = slot_start // 60
            start_mm = slot_start % 60
            end_hh = slot_end // 60
            end_mm = slot_end % 60
            time_range = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
            return (day, time_range)
    
    return (day, "No suitable time found")

# Define participants' schedules in (HH, MM) format
participants_schedules = {
    "Emily": [
        ((10, 0), (10, 30)),
        ((11, 30), (12, 30)),
        ((14, 0), (15, 0)),
        ((16, 0), (16, 30)),
    ],
    "Melissa": [
        ((9, 30), (10, 0)),
        ((14, 30), (15, 0)),
    ],
    "Frank": [
        ((10, 0), (10, 30)),
        ((11, 0), (11, 30)),
        ((12, 30), (13, 0)),
        ((13, 30), (14, 30)),
        ((15, 0), (16, 0)),
        ((16, 30), (17, 0)),
    ],
}

# Frank's preference: no meetings after 9:30
preferences = {
    "Frank": (9, 30),
}

# Work hours: 9:00 to 17:00
work_hours = (9, 17)

# Meeting duration: 30 minutes
duration = 30

# Find the meeting time
day, time_range = find_meeting_time(participants_schedules, duration, work_hours, preferences)
print(f"{day}: {time_range}")