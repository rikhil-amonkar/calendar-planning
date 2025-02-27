def find_meeting_time():
    # Define Patrick's busy intervals in hours as tuples (start, end)
    busy_times = [
        (9, 9.5),   # 9:00 to 9:30
        (10.5, 12), # 10:30 to 12:00
        (12.5, 13.5), # 12:30 to 13:30
        (14, 14.5),  # 14:00 to 14:30
        (15, 16.5)   # 15:00 to 16:30
    ]
    
    # Work hours in hours (9:00 to 17:00)
    start_day = 9
    end_day = 17
    
    # Check each possible 30-minute slot starting from the beginning of the day
    current_time = start_day
    while current_time < end_day:
        # Calculate end time of the current slot
        end_time = current_time + 0.5
        
        # Check if this slot is available (does not overlap with any busy time)
        is_available = True
        for busy_start, busy_end in busy_times:
            # Check if the current slot overlaps with any busy time
            if not (end_time <= busy_start or current_time >= busy_end):
                is_available = False
                break
        
        if is_available:
            # Convert times back to hours:minutes format
            start_hour = int(current_time)
            start_minute = int(round((current_time - start_hour) * 60, 0))
            end_hour = int(end_time)
            end_minute = int(round((end_time - end_hour) * 60, 0))
            
            return f"Monday, {start_hour:02d}:{start_minute:02d} - {end_hour:02d}:{end_minute:02d}"
        
        # Move to the next possible slot
        current_time = end_time
    
    # If no slot found (though in this problem, it should always find one)
    return "No available time slot found."

# Execute the function
print(find_meeting_time())
