def find_meeting_time(participants_schedules, duration_minutes, work_hours_start, work_hours_end, preferences=None):
    """
    Find a meeting time that fits all participants' schedules and constraints.
    
    Args:
        participants_schedules: Dict of participants with their busy times in 24h format.
        duration_minutes: Duration of the meeting in minutes.
        work_hours_start: Start of work hours in 24h format (e.g., '9:00').
        work_hours_end: End of work hours in 24h format (e.g., '17:00').
        preferences: Optional dict of preferences (e.g., 'no_after' time).
    
    Returns:
        A tuple of (day, start_time, end_time) if found, else None.
    """
    # Convert work hours to minutes since midnight
    work_start = sum(x * int(t) for x, t in zip([60, 1], work_hours_start.split(':')))
    work_end = sum(x * int(t) for x, t in zip([60, 1], work_hours_end.split(':')))
    
    # Collect all busy intervals
    busy_intervals = []
    for participant, schedules in participants_schedules.items():
        for interval in schedules:
            start, end = interval.split(' to ')
            start_min = sum(x * int(t) for x, t in zip([60, 1], start.split(':')))
            end_min = sum(x * int(t) for x, t in zip([60, 1], end.split(':')))
            busy_intervals.append((start_min, end_min))
    
    # Sort intervals by start time
    busy_intervals.sort()
    
    # Merge overlapping or adjacent intervals
    merged = []
    for interval in busy_intervals:
        if not merged:
            merged.append(interval)
        else:
            last_start, last_end = merged[-1]
            current_start, current_end = interval
            if current_start <= last_end:
                new_interval = (last_start, max(last_end, current_end))
                merged[-1] = new_interval
            else:
                merged.append(interval)
    
    # Find available slots
    available_slots = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))
    
    # Filter slots by duration and preferences
    for slot in available_slots:
        slot_start, slot_end = slot
        if slot_end - slot_start >= duration_minutes:
            # Check preferences (e.g., no meetings after 14:00)
            if preferences and 'no_after' in preferences:
                no_after = sum(x * int(t) for x, t in zip([60, 1], preferences['no_after'].split(':')))
                if slot_start >= no_after:
                    continue
            return slot_start, slot_end
    
    return None

def minutes_to_time(minutes):
    """Convert minutes since midnight to HH:MM format."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define participants' schedules
participants_schedules = {
    'Jeffrey': ['9:30 to 10:00', '10:30 to 11:00'],
    'Virginia': ['9:00 to 9:30', '10:00 to 10:30', '14:30 to 15:00', '16:00 to 16:30'],
    'Melissa': ['9:00 to 11:30', '12:00 to 12:30', '13:00 to 15:00', '16:00 to 17:00']
}

# Define preferences
preferences = {'no_after': '14:00'}  # Melissa's preference

# Find meeting time
meeting_duration = 30  # minutes
work_hours_start = '9:00'
work_hours_end = '17:00'

result = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end, preferences)

if result:
    start_min, end_min = result
    start_time = minutes_to_time(start_min)
    end_time = minutes_to_time(start_min + meeting_duration)
    print(f"Monday:{start_time}:{end_time}")
else:
    print("No suitable time found.")