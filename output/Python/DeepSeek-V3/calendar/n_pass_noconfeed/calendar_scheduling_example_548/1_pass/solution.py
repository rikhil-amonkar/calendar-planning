def find_meeting_time(participants_schedules, preferences, duration, work_hours_start, work_hours_end, day):
    # Convert time strings to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration_min = duration * 60
    
    # Collect all busy intervals for all participants
    busy_intervals = []
    for participant, schedule in participants_schedules.items():
        for busy in schedule:
            start, end = map(time_to_minutes, busy.split(' to '))
            busy_intervals.append((start, end))
    
    # Add preference constraints as busy intervals
    for participant, pref in preferences.items():
        if pref.get('not_before'):
            not_before = time_to_minutes(pref['not_before'])
            busy_intervals.append((work_start, not_before))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Find free slots by checking gaps between busy intervals
    free_slots = []
    prev_end = work_start
    
    for start, end in busy_intervals:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    # Check the slot after the last busy interval
    if prev_end < work_end:
        free_slots.append((prev_end, work_end))
    
    # Find the first free slot that can accommodate the meeting
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= duration_min:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_min
            return (minutes_to_time(meeting_start), minutes_to_time(meeting_end))
    
    return None

# Define the problem parameters
participants_schedules = {
    'Judy': [],
    'Nicole': ['9:00 to 10:00', '10:30 to 16:30']
}

preferences = {
    'Nicole': {'not_before': '16:00'}
}

duration = 0.5  # half an hour
work_hours_start = '9:00'
work_hours_end = '17:00'
day = 'Monday'

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, preferences, duration, work_hours_start, work_hours_end, day)

# Output the result
if meeting_time:
    start, end = meeting_time
    print(f"{day}:{start}:{end}")
else:
    print("No suitable time found.")