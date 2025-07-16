def find_meeting_time(participants_busy, preferences, day, work_hours, duration):
    # Convert work hours to minutes
    start_hour, end_hour = work_hours
    start_time = start_hour * 60
    end_time = end_hour * 60
    
    # Initialize a list to keep track of busy times for all participants
    all_busy = []
    
    # Combine all busy times
    for person in participants_busy:
        all_busy.extend(participants_busy[person])
    
    # Also add preference constraints (like Janice not wanting to meet after 13:00)
    for person in preferences:
        if person == 'Janice' and 'not_after' in preferences[person]:
            not_after_time = preferences[person]['not_after']
            not_after_minutes = not_after_time[0] * 60 + not_after_time[1]
            all_busy.append((not_after_minutes, end_time))
    
    # Sort all busy intervals
    all_busy.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged_busy = []
    for start, end in all_busy:
        if not merged_busy:
            merged_busy.append((start, end))
        else:
            last_start, last_end = merged_busy[-1]
            if start <= last_end:
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged_busy[-1] = (new_start, new_end)
            else:
                merged_busy.append((start, end))
    
    # Find available slots
    available_slots = []
    previous_end = start_time
    
    for start, end in merged_busy:
        if start > previous_end:
            available_slots.append((previous_end, start))
        previous_end = max(previous_end, end)
    
    if previous_end < end_time:
        available_slots.append((previous_end, end_time))
    
    # Check each available slot for duration
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration:
            # Convert back to HH:MM format
            start_hh = slot_start // 60
            start_mm = slot_start % 60
            end_hh = (slot_start + duration) // 60
            end_mm = (slot_start + duration) % 60
            return f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
    
    return None

# Define participants' busy times in minutes
participants_busy = {
    'Christine': [
        (9 * 60 + 30, 10 * 60 + 30),
        (12 * 60 + 0, 12 * 60 + 30),
        (13 * 60 + 0, 13 * 60 + 30),
        (14 * 60 + 30, 15 * 60 + 0),
        (16 * 60 + 0, 16 * 60 + 30)
    ],
    'Bobby': [
        (12 * 60 + 0, 12 * 60 + 30),
        (14 * 60 + 30, 15 * 60 + 0)
    ],
    'Elizabeth': [
        (9 * 60 + 0, 9 * 60 + 30),
        (11 * 60 + 30, 13 * 60 + 0),
        (13 * 60 + 30, 14 * 60 + 0),
        (15 * 60 + 0, 15 * 60 + 30),
        (16 * 60 + 0, 17 * 60 + 0)
    ],
    'Tyler': [
        (9 * 60 + 0, 11 * 60 + 0),
        (12 * 60 + 0, 12 * 60 + 30),
        (13 * 60 + 0, 13 * 60 + 30),
        (15 * 60 + 30, 16 * 60 + 0),
        (16 * 60 + 30, 17 * 60 + 0)
    ],
    'Edward': [
        (9 * 60 + 0, 9 * 60 + 30),
        (10 * 60 + 0, 11 * 60 + 0),
        (11 * 60 + 30, 14 * 60 + 0),
        (14 * 60 + 30, 15 * 60 + 30),
        (16 * 60 + 0, 17 * 60 + 0)
    ]
}

# Janice's preference: not after 13:00
preferences = {
    'Janice': {'not_after': (13, 0)}
}

# Meeting parameters
day = 'Monday'
work_hours = (9, 17)  # 9:00 to 17:00
duration = 30  # minutes

# Find the meeting time
meeting_time = find_meeting_time(participants_busy, preferences, day, work_hours, duration)

# Output the result
print(f"{day}: {meeting_time}")