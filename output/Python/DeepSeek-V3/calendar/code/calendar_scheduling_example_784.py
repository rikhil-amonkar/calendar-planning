def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_duration = 60  # minutes
    
    # Define blocked times for each participant per day in minutes since midnight
    blocked_times = {
        'Judith': {
            'Monday': [(12 * 60, 12 * 60 + 30)],  # 12:00-12:30
            'Wednesday': [(11 * 60 + 30, 12 * 60)]  # 11:30-12:00
        },
        'Timothy': {
            'Monday': [
                (9 * 60 + 30, 10 * 60),        # 9:30-10:00
                (10 * 60 + 30, 11 * 60 + 30),  # 10:30-11:30
                (12 * 60 + 30, 14 * 60),       # 12:30-14:00
                (15 * 60 + 30, 17 * 60)        # 15:30-17:00
            ],
            'Tuesday': [
                (9 * 60 + 30, 13 * 60),        # 9:30-13:00
                (13 * 60 + 30, 14 * 60),       # 13:30-14:00
                (14 * 60 + 30, 17 * 60)        # 14:30-17:00
            ],
            'Wednesday': [
                (9 * 60, 9 * 60 + 30),         # 9:00-9:30
                (10 * 60 + 30, 11 * 60),      # 10:30-11:00
                (13 * 60 + 30, 14 * 60 + 30),  # 13:30-14:30
                (15 * 60, 15 * 60 + 30),       # 15:00-15:30
                (16 * 60, 16 * 60 + 30)        # 16:00-16:30
            ]
        }
    }
    
    # Judith's preferences: avoid Monday and Wednesday before 12:00
    preferred_days = ['Tuesday', 'Wednesday']
    
    # Iterate through days in preferred order
    for day in preferred_days:
        if day == 'Wednesday':
            # On Wednesday, Judith prefers after 12:00
            start_time = max(work_start, 12 * 60)
        else:
            start_time = work_start
        
        # Generate all possible slots for the day
        current_time = start_time
        while current_time + meeting_duration <= work_end:
            slot_end = current_time + meeting_duration
            conflict = False
            
            # Check Judith's availability
            for block_start, block_end in blocked_times['Judith'].get(day, []):
                if not (slot_end <= block_start or current_time >= block_end):
                    conflict = True
                    break
            
            # Check Timothy's availability if no conflict yet
            if not conflict:
                for block_start, block_end in blocked_times['Timothy'].get(day, []):
                    if not (slot_end <= block_start or current_time >= block_end):
                        conflict = True
                        break
            
            if not conflict:
                # Format the time as HH:MM:HH:MM
                start_str = f"{current_time // 60:02d}:{current_time % 60:02d}"
                end_str = f"{slot_end // 60:02d}:{slot_end % 60:02d}"
                return f"{day}: {start_str}:{end_str}"
            
            current_time += 15  # Check in 15-minute increments
    
    # If no preferred day works, check Monday (though Judith prefers to avoid)
    day = 'Monday'
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        slot_end = current_time + meeting_duration
        conflict = False
        
        # Check Judith's availability
        for block_start, block_end in blocked_times['Judith'].get(day, []):
            if not (slot_end <= block_start or current_time >= block_end):
                conflict = True
                break
        
        # Check Timothy's availability if no conflict yet
        if not conflict:
            for block_start, block_end in blocked_times['Timothy'].get(day, []):
                if not (slot_end <= block_start or current_time >= block_end):
                    conflict = True
                    break
        
        if not conflict:
            # Format the time as HH:MM:HH:MM
            start_str = f"{current_time // 60:02d}:{current_time % 60:02d}"
            end_str = f"{slot_end // 60:02d}:{slot_end % 60:02d}"
            return f"{day}: {start_str}:{end_str}"
        
        current_time += 15  # Check in 15-minute increments
    
    return "No suitable time found."

# Run the function and print the result
print(find_meeting_time())