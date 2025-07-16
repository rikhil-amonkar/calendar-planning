def find_meeting_time():
    # Define work hours and days to consider
    work_hours_start = 9 * 60  # 9:00 in minutes
    work_hours_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    
    # Define Ruth's busy times in minutes since midnight for each day
    ruth_busy = {
        'Monday': [(9 * 60, 17 * 60)],
        'Tuesday': [(9 * 60, 17 * 60)],
        'Wednesday': [(9 * 60, 17 * 60)],
        'Thursday': [(9 * 60, 11 * 60), (11 * 60 + 30, 14 * 60 + 30), (15 * 60, 17 * 60)],
    }
    
    # Julie's preference: avoid Thursday before 11:30
    julie_preference = {
        'Thursday': (9 * 60, 11 * 60 + 30)
    }
    
    meeting_duration = 30  # minutes
    
    # Iterate through each day to find a suitable time
    for day in days:
        if day not in ruth_busy:
            continue  # Ruth is free all day (not the case here)
        
        # Get Ruth's busy slots for the day
        busy_slots = ruth_busy[day]
        
        # Generate free slots for Ruth by inverting busy slots
        free_slots = []
        prev_end = work_hours_start
        
        for start, end in sorted(busy_slots):
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = end
        
        if prev_end < work_hours_end:
            free_slots.append((prev_end, work_hours_end))
        
        # Check Julie's preference for Thursday
        if day in julie_preference:
            avoid_start, avoid_end = julie_preference[day]
            # Filter out free slots that overlap with Julie's preference
            new_free_slots = []
            for slot_start, slot_end in free_slots:
                # Slot is entirely outside avoid time
                if slot_end <= avoid_start or slot_start >= avoid_end:
                    new_free_slots.append((slot_start, slot_end))
                else:
                    # Split slot if it overlaps with avoid time
                    if slot_start < avoid_start:
                        new_free_slots.append((slot_start, avoid_start))
                    if slot_end > avoid_end:
                        new_free_slots.append((avoid_end, slot_end))
            free_slots = new_free_slots
        
        # Check each free slot for sufficient duration
        for slot_start, slot_end in free_slots:
            if slot_end - slot_start >= meeting_duration:
                # Found a suitable slot
                meeting_start = slot_start
                meeting_end = meeting_start + meeting_duration
                
                # Convert minutes back to HH:MM format
                def minutes_to_time(minutes):
                    hours = minutes // 60
                    mins = minutes % 60
                    return f"{hours:02d}:{mins:02d}"
                
                time_range = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
                return day, time_range
    
    return None, None

day, time_range = find_meeting_time()
print(f"{day}: {time_range}")