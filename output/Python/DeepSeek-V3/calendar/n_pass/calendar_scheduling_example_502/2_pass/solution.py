def find_meeting_time(participants_busy, preferences, work_hours, duration):
    # Convert all time strings to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start, work_end = map(time_to_minutes, work_hours.split(' to '))
    duration_min = duration * 60
    
    # Combine all busy times and sort them
    all_busy = []
    for person in participants_busy:
        for busy_range in participants_busy[person]:
            start, end = map(time_to_minutes, busy_range.split(' to '))
            all_busy.append((start, end))
    all_busy.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged_busy = []
    for start, end in all_busy:
        if not merged_busy:
            merged_busy.append([start, end])
        else:
            last_start, last_end = merged_busy[-1]
            if start <= last_end:
                merged_busy[-1][1] = max(end, last_end)
            else:
                merged_busy.append([start, end])
    
    # Find available slots
    available = []
    prev_end = work_start
    for start, end in merged_busy:
        if start > prev_end:
            available.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available.append((prev_end, work_end))
    
    # Filter based on preferences
    preferred_slots = []
    avoid_after = preferences.get('avoid_after', None)
    avoid_after_min = time_to_minutes(avoid_after) if avoid_after else None
    
    for slot_start, slot_end in available:
        slot_duration = slot_end - slot_start
        if slot_duration >= duration_min:
            if avoid_after_min is None or slot_start < avoid_after_min:
                preferred_slots.append((slot_start, slot_end))
    
    # Select the first available preferred slot
    if preferred_slots:
        for slot_start, slot_end in preferred_slots:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_min
            if meeting_end <= slot_end:
                return (minutes_to_time(meeting_start), minutes_to_time(meeting_end))
    
    return None

# Define the problem
participants_busy = {
    'Jack': [
        '09:30 to 10:30',
        '11:00 to 11:30',
        '12:30 to 13:00',
        '14:00 to 14:30',
        '16:00 to 16:30'
    ],
    'Charlotte': [
        '09:30 to 10:00',
        '10:30 to 12:00',
        '12:30 to 13:30',
        '14:00 to 16:00'
    ]
}

preferences = {
    'avoid_after': '12:30'
}

work_hours = '09:00 to 17:00'
duration = 0.5  # in hours

# Find the meeting time
meeting_time = find_meeting_time(participants_busy, preferences, work_hours, duration)
if meeting_time:
    start_time, end_time = meeting_time
    print(f"{{{start_time}:{end_time}}}")
    print("Monday")
else:
    print("No suitable time found.")