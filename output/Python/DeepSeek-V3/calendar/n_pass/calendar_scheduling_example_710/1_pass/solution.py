def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Define busy times for each participant in minutes since midnight
    # Format: {day: [(start1, end1), (start2, end2), ...]}
    cheryl_busy = {
        'Monday': [(9*60, 9*60 + 30), (11*60 + 30, 13*60), (15*60 + 30, 16*60)],
        'Tuesday': [(15*60, 15*60 + 30)],
        'Wednesday': []  # Cheryl can't meet on Wednesday
    }
    
    kyle_busy = {
        'Monday': [(9*60, 17*60)],
        'Tuesday': [(9*60 + 30, 17*60)],
        'Wednesday': [(9*60, 9*60 + 30), (10*60, 13*60), (13*60 + 30, 14*60), (14*60 + 30, 17*60)]
    }
    
    # Iterate through each day
    for day in days:
        if day == 'Wednesday':
            continue  # Cheryl can't meet on Wednesday
        
        # Combine and sort all busy intervals for the day
        all_busy = cheryl_busy[day] + kyle_busy[day]
        all_busy.sort()
        
        # Find free slots
        free_slots = []
        prev_end = work_start
        
        for start, end in all_busy:
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        if prev_end < work_end:
            free_slots.append((prev_end, work_end))
        
        # Check each free slot for availability
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
if day and time_range:
    print(f"{day}: {time_range}")
else:
    print("No suitable time found.")