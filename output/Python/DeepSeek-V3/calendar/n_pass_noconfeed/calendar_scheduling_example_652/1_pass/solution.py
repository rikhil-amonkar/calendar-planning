def find_meeting_time():
    # Define work hours and days
    work_hours_start = 9 * 60  # 9:00 in minutes
    work_hours_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday']
    
    # Define busy slots for each person on each day in minutes since midnight
    jesse_busy = {
        'Monday': [(13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60)],
        'Tuesday': [(9 * 60, 9 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60, 15 * 60)]
    }
    
    lawrence_busy = {
        'Monday': [(9 * 60, 17 * 60)],  # Entire day busy
        'Tuesday': [
            (9 * 60 + 30, 10 * 60 + 30),
            (11 * 60 + 30, 12 * 60 + 30),
            (13 * 60, 13 * 60 + 30),
            (14 * 60 + 30, 15 * 60),
            (15 * 60 + 30, 16 * 60 + 30)
        ]
    }
    
    # Lawrence cannot meet on Tuesday after 16:30
    lawrence_no_meet_after = 16 * 60 + 30
    
    meeting_duration = 30  # minutes
    
    # Iterate through each day
    for day in days:
        if day == 'Monday' and lawrence_busy['Monday'][0][0] == work_hours_start and lawrence_busy['Monday'][0][1] == work_hours_end:
            continue  # Lawrence is busy all day on Monday
        
        # Combine and sort all busy slots for the day
        busy_slots = []
        if day == 'Monday':
            busy_slots.extend(jesse_busy['Monday'])
        else:
            busy_slots.extend(jesse_busy['Tuesday'])
            busy_slots.extend(lawrence_busy['Tuesday'])
        
        # Sort busy slots by start time
        busy_slots.sort()
        
        # Find free slots
        free_slots = []
        prev_end = work_hours_start
        
        for slot in busy_slots:
            if slot[0] > prev_end:
                free_slots.append((prev_end, slot[0]))
            prev_end = max(prev_end, slot[1])
        
        # Check after last busy slot
        if prev_end < work_hours_end:
            free_slots.append((prev_end, work_hours_end))
        
        # Check each free slot for availability
        for slot in free_slots:
            start, end = slot
            # Adjust end time if it's Tuesday and Lawrence cannot meet after 16:30
            if day == 'Tuesday':
                end = min(end, lawrence_no_meet_after)
            
            if end - start >= meeting_duration:
                # Found a suitable slot
                meeting_start = start
                meeting_end = meeting_start + meeting_duration
                
                # Convert back to HH:MM format
                def minutes_to_time(minutes):
                    hours = minutes // 60
                    mins = minutes % 60
                    return f"{hours:02d}:{mins:02d}"
                
                time_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
                return day, time_str
    
    return None, None

day, time_str = find_meeting_time()
print(f"{day}: {time_str}")