def find_meeting_time(participants_schedules, preferences, duration, work_hours):
    # Convert all time strings to minutes since 9:00 (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hh = int(minutes // 60)  # Ensure hh is integer
        mm = int(minutes % 60)   # Ensure mm is integer
        return f"{hh:02d}:{mm:02d}"
    
    start_work, end_work = work_hours
    start_min = time_to_minutes(start_work)
    end_min = time_to_minutes(end_work)
    duration_min = duration * 60
    
    # Initialize the free slots for all participants
    free_slots = []
    for participant in participants_schedules:
        busy_slots = participants_schedules[participant]
        participant_free = []
        prev_end = start_min
        
        # Sort busy slots by start time
        busy_sorted = sorted(busy_slots, key=lambda x: time_to_minutes(x[0]))
        
        for busy_start, busy_end in busy_sorted:
            busy_start_min = time_to_minutes(busy_start)
            busy_end_min = time_to_minutes(busy_end)
            
            if prev_end < busy_start_min:
                participant_free.append((prev_end, busy_start_min))
            prev_end = max(prev_end, busy_end_min)
        
        if prev_end < end_min:
            participant_free.append((prev_end, end_min))
        
        free_slots.append(participant_free)
    
    # Find common free slots
    common_free = free_slots[0]
    for participant_free in free_slots[1:]:
        new_common = []
        i = j = 0
        while i < len(common_free) and j < len(participant_free):
            start1, end1 = common_free[i]
            start2, end2 = participant_free[j]
            
            start_max = max(start1, start2)
            end_min = min(end1, end2)
            
            if start_max < end_min:
                new_common.append((start_max, end_min))
            
            if end1 < end2:
                i += 1
            else:
                j += 1
        common_free = new_common
    
    # Apply preferences
    preferred_slots = []
    avoid_after = preferences.get('avoid_after', None)
    avoid_after_min = time_to_minutes(avoid_after) if avoid_after else end_min
    
    for start, end in common_free:
        if start < avoid_after_min:
            preferred_slots.append((start, min(end, avoid_after_min)))
    
    # Find the first slot that fits the duration
    for start, end in preferred_slots:
        if end - start >= duration_min:
            meeting_start = start
            meeting_end = start + duration_min
            return minutes_to_time(meeting_start), minutes_to_time(meeting_end)
    
    return None

# Define the participants' schedules
participants_schedules = {
    'Raymond': [('9:00', '9:30'), ('11:30', '12:00'), ('13:00', '13:30'), ('15:00', '15:30')],
    'Billy': [('10:00', '10:30'), ('12:00', '13:00'), ('16:30', '17:00')],
    'Donald': [('9:00', '9:30'), ('10:00', '11:00'), ('12:00', '13:00'), ('14:00', '14:30'), ('16:00', '17:00')]
}

# Define preferences
preferences = {
    'avoid_after': '15:00'
}

# Meeting duration in hours
duration = 0.5  # 30 minutes

# Work hours
work_hours = ('9:00', '17:00')

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, preferences, duration, work_hours)

if meeting_time:
    start, end = meeting_time
    print(f"{{{start}:{end}}}")
    print("Monday")
else:
    print("No suitable time found.")