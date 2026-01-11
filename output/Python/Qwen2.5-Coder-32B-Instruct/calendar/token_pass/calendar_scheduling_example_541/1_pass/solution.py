def find_meeting_time(kayla_busy, rebecca_busy, meeting_duration, day):
    # Define the full working day
    start_of_day = 9 * 60  # 9:00 AM in minutes
    end_of_day = 17 * 60   # 5:00 PM in minutes
    
    # Convert busy times to minutes since start of the day
    kayla_busy_minutes = [(start * 60, end * 60) for start, end in kayla_busy]
    rebecca_busy_minutes = [(start * 60, end * 60) for start, end in rebecca_busy]
    
    # Function to find free periods
    def find_free_periods(busy_times, start, end):
        free_periods = []
        current_start = start
        
        for busy_start, busy_end in sorted(busy_times):
            if current_start < busy_start:
                free_periods.append((current_start, busy_start))
            current_start = max(current_start, busy_end)
        
        if current_start < end:
            free_periods.append((current_start, end))
        
        return free_periods
    
    # Find free periods for both participants
    kayla_free = find_free_periods(kayla_busy_minutes, start_of_day, end_of_day)
    rebecca_free = find_free_periods(rebecca_busy_minutes, start_of_day, end_of_day)
    
    # Find common free periods
    common_free = []
    i, j = 0, 0
    
    while i < len(kayla_free) and j < len(rebecca_free):
        k_start, k_end = kayla_free[i]
        r_start, r_end = rebecca_free[j]
        
        # Find intersection
        overlap_start = max(k_start, r_start)
        overlap_end = min(k_end, r_end)
        
        if overlap_end - overlap_start >= meeting_duration:
            common_free.append((overlap_start, overlap_end))
        
        # Move to the next period
        if k_end <= r_end:
            i += 1
        else:
            j += 1
    
    # If a suitable slot is found, format and return it
    if common_free:
        start, end = common_free[0]  # Take the first available slot
        start_hour, start_minute = divmod(start, 60)
        end_hour, end_minute = divmod(end, 60)
        return f"{start_hour:02}:{start_minute:02}:{end_hour:02}:{end_minute:02} {day}"
    
    return "No suitable time found"

# Given data
kayla_busy = [(10, 10.5), (14.5, 16)]
rebecca_busy = [(9, 13), (13.5, 15), (15.5, 16)]

# Meeting duration in hours
meeting_duration = 1 * 60  # 1 hour

# Day of the week
day = "Monday"

# Find and print the meeting time
print(find_meeting_time(kayla_busy, rebecca_busy, meeting_duration, day))