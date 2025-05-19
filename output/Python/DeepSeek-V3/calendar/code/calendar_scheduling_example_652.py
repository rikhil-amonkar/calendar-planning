def find_meeting_time():
    # Define work hours and days
    work_hours_start = 9 * 60  # 9:00 in minutes
    work_hours_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday']
    
    # Define participants' busy slots in minutes since midnight
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
    lawrence_additional_constraint = {
        'Tuesday': (16 * 60 + 30, work_hours_end)
    }
    
    meeting_duration = 30  # minutes
    
    # Iterate through each day
    for day in days:
        # Skip Monday for Lawrence since he's busy all day
        if day == 'Monday':
            continue
        
        # Combine all busy slots for both participants
        all_busy = jesse_busy[day] + lawrence_busy[day]
        
        # Add Lawrence's additional constraint if applicable
        if day in lawrence_additional_constraint:
            all_busy.append(lawrence_additional_constraint[day])
        
        # Sort all busy slots by start time
        all_busy.sort()
        
        # Check for available slots
        prev_end = work_hours_start
        for busy_start, busy_end in all_busy:
            if busy_start > prev_end:
                available_start = prev_end
                available_end = busy_start
                if available_end - available_start >= meeting_duration:
                    # Found a suitable slot
                    start_h = available_start // 60
                    start_m = available_start % 60
                    end_h = (available_start + meeting_duration) // 60
                    end_m = (available_start + meeting_duration) % 60
                    return day, f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
            prev_end = max(prev_end, busy_end)
        
        # Check after the last busy slot
        if work_hours_end - prev_end >= meeting_duration:
            start_h = prev_end // 60
            start_m = prev_end % 60
            end_h = (prev_end + meeting_duration) // 60
            end_m = (prev_end + meeting_duration) % 60
            return day, f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    
    return None, None

day, time_slot = find_meeting_time()
print(f"{day}: {time_slot}")