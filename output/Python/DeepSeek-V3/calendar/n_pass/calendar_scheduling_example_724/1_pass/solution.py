def find_meeting_time():
    # Define work hours and days to consider
    work_hours_start = 9 * 60  # 9:00 in minutes
    work_hours_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Define the duration of the meeting in minutes
    meeting_duration = 30
    
    # Define the busy times for each participant in minutes since midnight
    # Format: {day: [(start1, end1), (start2, end2), ...]}
    tyler_busy = {
        'Tuesday': [(9 * 60, 9 * 60 + 30), (14 * 60 + 30, 15 * 60)],
        'Wednesday': [(10 * 60 + 30, 11 * 60), (12 * 60 + 30, 13 * 60), 
                     (13 * 60 + 30, 14 * 60), (16 * 60 + 30, 17 * 60)]
    }
    
    ruth_busy = {
        'Monday': [(9 * 60, 10 * 60), (10 * 60 + 30, 12 * 60), 
                   (12 * 60 + 30, 14 * 60 + 30), (15 * 60, 16 * 60), 
                   (16 * 60 + 30, 17 * 60)],
        'Tuesday': [(9 * 60, 17 * 60)],
        'Wednesday': [(9 * 60, 17 * 60)]
    }
    
    # Tyler's preference: avoid Monday before 16:00
    tyler_preference = {
        'Monday': (9 * 60, 16 * 60)
    }
    
    # Iterate through each day to find a suitable time
    for day in days:
        # Skip if Ruth is entirely busy (Tuesday and Wednesday)
        if day in ruth_busy and any(start == work_hours_start and end == work_hours_end 
                                   for start, end in ruth_busy[day]):
            continue
        
        # Combine all busy times for Tyler and Ruth on this day
        combined_busy = []
        if day in tyler_busy:
            combined_busy.extend(tyler_busy[day])
        if day in ruth_busy:
            combined_busy.extend(ruth_busy[day])
        
        # Sort the busy times by start time
        combined_busy.sort()
        
        # Check the time before the first busy block
        prev_end = work_hours_start
        for start, end in combined_busy:
            if start - prev_end >= meeting_duration:
                # Check Tyler's preference for Monday
                if day == 'Monday':
                    preference_start, preference_end = tyler_preference['Monday']
                    # Check if the proposed time is entirely after preference_end
                    if prev_end >= preference_end:
                        return day, prev_end, prev_end + meeting_duration
                    # Check if the proposed time starts before preference_end but ends after
                    elif prev_end + meeting_duration > preference_end:
                        return day, preference_end, preference_end + meeting_duration
                    else:
                        # Skip this slot if it's before preference_end
                        pass
                else:
                    return day, prev_end, prev_end + meeting_duration
            prev_end = max(prev_end, end)
        
        # Check the time after the last busy block
        if work_hours_end - prev_end >= meeting_duration:
            # Check Tyler's preference for Monday
            if day == 'Monday':
                preference_start, preference_end = tyler_preference['Monday']
                if prev_end >= preference_end:
                    return day, prev_end, prev_end + meeting_duration
                elif prev_end + meeting_duration > preference_end:
                    return day, preference_end, preference_end + meeting_duration
                else:
                    pass
            else:
                return day, prev_end, prev_end + meeting_duration
    
    # If no time found (though the problem states there is a solution)
    return None

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Find the meeting time
result = find_meeting_time()
if result:
    day, start, end = result
    start_time = format_time(start)
    end_time = format_time(end)
    print(f"{day}:{start_time}:{end_time}")
else:
    print("No suitable time found.")