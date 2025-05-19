def find_meeting_time():
    # Define the working hours
    work_hours = [(9, 17)]  # Monday
    # Meeting duration
    duration = 30  # 30 minutes
    
    # Available day
    available_day = 'Monday'
    
    # Define blocked times for each person
    blocked_times = {
        'Diane': {
            'Monday': [(9 * 60 + 30, 10 * 60), (14 * 60 + 30, 15 * 60)]
        },
        'Jack': {
            'Monday': [(13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60)]
        },
        'Eugene': {
            'Monday': [(9 * 60, 10 * 60), (10 * 60 + 30, 11 * 60), (12 * 60, 14 * 60 + 30), (15 * 60, 16 * 60 + 30)]
        },
        'Patricia': {
            'Monday': [(9 * 60 + 30, 10 * 60 + 30), (11 * 60, 12 * 60), (12 * 60 + 30, 14 * 60), (15 * 60, 16 * 60 + 30)]
        }
    }
    
    # Convert day to numerical value
    day_num = {'Monday': 0}
    
    # Check each time slot in the working hours
    for hour in range(9, 17):
        for minute in range(0, 60):
            start = hour * 60 + minute
            end = start + duration
            
            # Check if the time slot is within working hours
            if start < 9 * 60 or end > 17 * 60:
                continue
            
            # Check against each person's blocked times
            all_available = True
            for person in ['Diane', 'Jack', 'Eugene', 'Patricia']:
                if person in blocked_times and day_num == 0:  # Only check for Monday
                    for block_start, block_end in blocked_times[person]['Monday']:
                        if block_start <= start < block_end:
                            all_available = False
                            break
                    if not all_available:
                        break
            
            if all_available:
                print(f"{start // 60:02d}:{start % 60:02d}-{end // 60:02d}:{end % 60:02d} Monday")
                return f"{start // 60:02d}:{start % 60:02d}-{end // 60:02d}:{end % 60:02d} Monday"
    
    # If no slot is found, return an error message
    return "No available time found."