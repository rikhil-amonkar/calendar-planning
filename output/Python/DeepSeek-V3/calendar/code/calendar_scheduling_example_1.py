def find_meeting_time(participants_schedules, preferences, duration, work_hours_start, work_hours_end):
    # Convert all time strings to minutes since 9:00 (work_hours_start)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return (hh - 9) * 60 + mm  # 9:00 is 0 minutes
    
    def minutes_to_time(minutes):
        hh = 9 + (minutes // 60)
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    
    # Collect all busy intervals for each participant
    busy_intervals = []
    for participant, schedules in participants_schedules.items():
        for start, end in schedules:
            busy_start = time_to_minutes(start)
            busy_end = time_to_minutes(end)
            busy_intervals.append((busy_start, busy_end))
    
    # Add preference constraints as busy intervals
    for participant, pref in preferences.items():
        if pref.get('avoid_after', None):
            avoid_after = time_to_minutes(pref['avoid_after'])
            busy_intervals.append((avoid_after, work_end))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Find all free intervals
    free_intervals = []
    prev_end = work_start
    for start, end in busy_intervals:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    
    # Find the first free interval that can accommodate the meeting
    for start, end in free_intervals:
        if end - start >= duration:
            meeting_start = start
            meeting_end = meeting_start + duration
            return (minutes_to_time(meeting_start), minutes_to_time(meeting_end))
    
    return None

# Define the participants' schedules
participants_schedules = {
    'Raymond': [('9:00', '9:30'), ('11:30', '12:00'), ('13:00', '13:30'), ('15:00', '15:30')],
    'Billy': [('10:00', '10:30'), ('12:00', '13:00'), ('16:30', '17:00')],
    'Donald': [('9:00', '9:30'), ('10:00', '11:00'), ('12:00', '13:00'), ('14:00', '14:30'), ('16:00', '17:00')]
}

# Define preferences
preferences = {
    'Billy': {'avoid_after': '15:00'}
}

# Meeting duration in minutes (30 minutes)
duration = 30

# Work hours
work_hours_start = '9:00'
work_hours_end = '17:00'

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, preferences, duration, work_hours_start, work_hours_end)

# Output the result
if meeting_time:
    start_time, end_time = meeting_time
    print(f"{{{start_time}:{end_time}}} Monday")
else:
    print("No suitable time found.")