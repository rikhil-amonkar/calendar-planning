def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_duration = 30  # minutes

    # Define busy slots for Nicole and Ruth in minutes since start of day
    nicole_busy = {
        'Monday': [(9*60, 9*60 + 30), (13*60, 13*60 + 30), (14*60 + 30, 15*60 + 30)],
        'Tuesday': [(9*60, 9*60 + 30), (11*60 + 30, 13*60 + 30), (14*60 + 30, 15*60 + 30)],
        'Wednesday': [(10*60, 11*60), (12*60 + 30, 15*60), (16*60, 17*60)]
    }
    
    ruth_busy = {
        'Monday': [(9*60, 17*60)],  # Entire day blocked
        'Tuesday': [(9*60, 17*60)],  # Entire day blocked
        'Wednesday': [
            (9*60, 10*60 + 30),
            (11*60, 11*60 + 30),
            (12*60, 12*60 + 30),
            (13*60 + 30, 15*60 + 30),
            (16*60, 16*60 + 30)
        ]
    }
    
    # Ruth's additional constraint: no meetings after 13:30 on Wednesday
    ruth_no_meet_after = 13 * 60 + 30  # 13:30 in minutes
    
    # Iterate through each day to find a suitable slot
    for day in days:
        if day == 'Wednesday':
            # Adjust work_end for Ruth on Wednesday
            effective_end = min(work_end, ruth_no_meet_after)
        else:
            effective_end = work_end
        
        # Generate all possible slots for the day
        possible_slots = []
        current_time = work_start
        
        # Merge and sort busy slots for both participants
        all_busy = nicole_busy.get(day, []) + ruth_busy.get(day, [])
        all_busy.sort()
        
        # Find free slots by checking gaps between busy slots
        for busy_start, busy_end in all_busy:
            if current_time < busy_start:
                possible_slots.append((current_time, busy_start))
            current_time = max(current_time, busy_end)
        
        # Check the slot after the last busy slot
        if current_time < effective_end:
            possible_slots.append((current_time, effective_end))
        
        # Check each possible slot for availability
        for slot_start, slot_end in possible_slots:
            slot_duration = slot_end - slot_start
            if slot_duration >= meeting_duration:
                # Found a suitable slot
                start_time = slot_start
                end_time = start_time + meeting_duration
                
                # Format the time as HH:MM
                def format_time(minutes):
                    hours = minutes // 60
                    mins = minutes % 60
                    return f"{hours:02d}:{mins:02d}"
                
                start_str = format_time(start_time)
                end_str = format_time(end_time)
                return f"{day}:{start_str}:{end_str}"
    
    return "No suitable time found."

# Run the function and print the result
print(find_meeting_time())