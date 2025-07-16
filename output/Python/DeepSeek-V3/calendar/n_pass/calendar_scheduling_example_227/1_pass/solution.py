def find_meeting_time(participants_busy_times, work_hours_start, work_hours_end, meeting_duration, preferences=None):
    """
    Find a meeting time that fits all participants' schedules and constraints.
    
    Args:
        participants_busy_times: Dict of participant names to their busy time slots.
        work_hours_start: Start of workday in "HH:MM" format.
        work_hours_end: End of workday in "HH:MM" format.
        meeting_duration: Duration of meeting in minutes.
        preferences: Optional dict of preferences (e.g., no meetings before a certain time).
    
    Returns:
        A tuple of (day, start_time, end_time) if a slot is found, else None.
    """
    # Convert time strings to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    
    # Collect all busy slots and merge overlapping ones
    all_busy_slots = []
    for busy_slots in participents_busy_times.values():
        for slot in busy_slots:
            start, end = map(time_to_minutes, slot.split(' to '))
            all_busy_slots.append((start, end))
    
    # Sort by start time
    all_busy_slots.sort()
    
    # Merge overlapping or adjacent slots
    merged_slots = []
    for start, end in all_busy_slots:
        if not merged_slots:
            merged_slots.append([start, end])
        else:
            last_start, last_end = merged_slots[-1]
            if start <= last_end:
                merged_slots[-1][1] = max(end, last_end)
            else:
                merged_slots.append([start, end])
    
    # Find available slots between work hours, excluding merged busy slots
    available_slots = []
    prev_end = work_start
    for start, end in merged_slots:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))
    
    # Check preferences (e.g., no meetings before a certain time)
    if preferences:
        pref_no_before = preferences.get('no_before', None)
        if pref_no_before:
            pref_min = time_to_minutes(pref_no_before)
            available_slots = [(s, e) for s, e in available_slots if s >= pref_min]
    
    # Find first available slot that fits the meeting duration
    for start, end in available_slots:
        if end - start >= meeting_duration:
            # Convert back to "HH:MM" format
            def minutes_to_time(minutes):
                hh = minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"
            
            meeting_start = minutes_to_time(start)
            meeting_end = minutes_to_time(start + meeting_duration)
            return meeting_start, meeting_end
    
    return None

# Define participants' busy times
participants_busy_times = {
    'Natalie': [],
    'David': ['11:30 to 12:00', '14:30 to 15:00'],
    'Douglas': ['9:30 to 10:00', '11:30 to 12:00', '13:00 to 13:30', '14:30 to 15:00'],
    'Ralph': ['9:00 to 9:30', '10:00 to 11:00', '11:30 to 12:30', '13:30 to 15:00', '15:30 to 16:00', '16:30 to 17:00'],
    'Jordan': ['9:00 to 10:00', '12:00 to 12:30', '13:00 to 13:30', '14:30 to 15:00', '15:30 to 17:00']
}

# Define preferences (David doesn't want to meet before 14:00)
preferences = {
    'no_before': '14:00'
}

# Find meeting time
meeting_time = find_meeting_time(
    participants_busy_times=participants_busy_times,
    work_hours_start='9:00',
    work_hours_end='17:00',
    meeting_duration=30,
    preferences=preferences
)

# Output result
if meeting_time:
    start, end = meeting_time
    print(f"{start}:{end}")
    print("Monday")
else:
    print("No suitable time found.")