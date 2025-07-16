def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    
    # Define days to consider and their constraints
    days = ["Monday", "Tuesday", "Wednesday"]
    avoid_days = {"Larry": ["Wednesday"], "Samuel": ["Tuesday"]}
    
    # Samuel's meetings in minutes since midnight for each day
    samuel_meetings = {
        "Monday": [
            (10 * 60 + 30, 11 * 60),      # 10:30-11:00
            (12 * 60, 12 * 60 + 30),       # 12:00-12:30
            (13 * 60, 15 * 60),            # 13:00-15:00
            (15 * 60 + 30, 16 * 60 + 30),  # 15:30-16:30
        ],
        "Tuesday": [
            (9 * 60, 12 * 60),             # 9:00-12:00
            (14 * 60, 15 * 60 + 30),       # 14:00-15:30
            (16 * 60 + 30, 17 * 60),      # 16:30-17:00
        ],
        "Wednesday": [
            (10 * 60 + 30, 11 * 60),      # 10:30-11:00
            (11 * 60 + 30, 12 * 60),       # 11:30-12:00
            (12 * 60 + 30, 13 * 60),       # 12:30-13:00
            (14 * 60, 14 * 60 + 30),       # 14:00-14:30
            (15 * 60, 16 * 60),            # 15:00-16:00
        ],
    }
    
    # Larry has no meetings, so only constrained by work hours and avoid_days
    meeting_duration = 30  # minutes
    
    # Iterate through days in order, respecting preferences
    for day in days:
        # Check if day is avoided by any participant
        if day in avoid_days["Larry"] or day in avoid_days["Samuel"]:
            continue
        
        # Get Samuel's meetings for the day
        meetings = samuel_meetings[day]
        
        # Find available slots for Samuel (gaps between meetings)
        available_slots = []
        prev_end = work_start
        
        for start, end in sorted(meetings):
            if start > prev_end:
                available_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        # Check after last meeting
        if prev_end < work_end:
            available_slots.append((prev_end, work_end))
        
        # Check each available slot for sufficient duration
        for slot_start, slot_end in available_slots:
            if slot_end - slot_start >= meeting_duration:
                # Found a suitable time
                start_time = slot_start
                end_time = start_time + meeting_duration
                
                # Convert times back to HH:MM format
                def minutes_to_time(minutes):
                    hours = minutes // 60
                    mins = minutes % 60
                    return f"{hours:02d}:{mins:02d}"
                
                time_str = f"{minutes_to_time(start_time)}:{minutes_to_time(end_time)}"
                return day, time_str
    
    return None, None

day, time_range = find_meeting_time()
print(f"{day}: {time_range}")