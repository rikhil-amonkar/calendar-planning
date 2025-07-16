def find_meeting_time():
    # Define work hours and days to consider
    work_hours_start = 9 * 60  # 9:00 in minutes
    work_hours_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    
    # Define Cheryl's preferences (avoid Wednesday and Thursday)
    cheryl_preferred_days = ['Monday', 'Tuesday']
    
    # Define James's schedule as a dictionary of days with busy time slots in minutes
    james_schedule = {
        'Monday': [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 11 * 60), 
                   (12 * 60 + 30, 13 * 60), (14 * 60 + 30, 15 * 60 + 30), 
                   (16 * 60 + 30, 17 * 60)],
        'Tuesday': [(9 * 60, 11 * 60), (11 * 60 + 30, 12 * 60), 
                    (12 * 60 + 30, 15 * 60 + 30), (16 * 60, 17 * 60)],
        'Wednesday': [(10 * 60, 11 * 60), (12 * 60, 13 * 60), 
                      (13 * 60 + 30, 16 * 60)],
        'Thursday': [(9 * 60 + 30, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), 
                     (13 * 60, 13 * 60 + 30), (14 * 60, 14 * 60 + 30), 
                     (16 * 60 + 30, 17 * 60)]
    }
    
    meeting_duration = 30  # minutes
    
    # Iterate through preferred days first (Monday, Tuesday)
    for day in cheryl_preferred_days:
        busy_slots = james_schedule[day]
        free_slots = []
        
        # Find free slots for James on this day
        previous_end = work_hours_start
        for start, end in sorted(busy_slots):
            if start > previous_end:
                free_slots.append((previous_end, start))
            previous_end = max(previous_end, end)
        if previous_end < work_hours_end:
            free_slots.append((previous_end, work_hours_end))
        
        # Check each free slot for availability
        for slot_start, slot_end in free_slots:
            if slot_end - slot_start >= meeting_duration:
                meeting_start = slot_start
                meeting_end = meeting_start + meeting_duration
                # Format the time as HH:MM:HH:MM
                start_time = f"{meeting_start // 60:02d}:{meeting_start % 60:02d}"
                end_time = f"{meeting_end // 60:02d}:{meeting_end % 60:02d}"
                print(f"{start_time}:{end_time} {day}")
                return
    
    # If no slot found in preferred days, check other days (not preferred by Cheryl)
    for day in [d for d in days if d not in cheryl_preferred_days]:
        busy_slots = james_schedule[day]
        free_slots = []
        
        # Find free slots for James on this day
        previous_end = work_hours_start
        for start, end in sorted(busy_slots):
            if start > previous_end:
                free_slots.append((previous_end, start))
            previous_end = max(previous_end, end)
        if previous_end < work_hours_end:
            free_slots.append((previous_end, work_hours_end))
        
        # Check each free slot for availability
        for slot_start, slot_end in free_slots:
            if slot_end - slot_start >= meeting_duration:
                meeting_start = slot_start
                meeting_end = meeting_start + meeting_duration
                # Format the time as HH:MM:HH:MM
                start_time = f"{meeting_start // 60:02d}:{meeting_start % 60:02d}"
                end_time = f"{meeting_end // 60:02d}:{meeting_end % 60:02d}"
                print(f"{start_time}:{end_time} {day}")
                return

find_meeting_time()