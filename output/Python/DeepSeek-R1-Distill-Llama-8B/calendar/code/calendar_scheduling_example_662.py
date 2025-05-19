def find_meeting_time():
    # Define the working hours
    work_hours = [(9, 17)]  # Monday
    # Meeting duration
    duration = 1  # 1 hour
    
    # Blocked times for each person on Monday
    blocked_times = {
        'Gary': {
            'Monday': [(9 * 60 + 30, 10 * 60), (11 * 60, 13 * 60), (14 * 60 + 30, 16 * 60)]
        },
        'David': {
            'Monday': [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (11 * 60, 12 * 60 + 30),
                      (13 * 60, 14 * 60 + 30), (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)]
        }
    }
    
    # Function to check availability
    def is_available(start, end, person):
        for block_start, block_end in blocked_times[person]['Monday']:
            if block_start <= start < block_end:
                return False
        return True
    
    # Check each possible start time
    for hour in range(9, 17):
        for minute in range(0, 60):
            start = hour * 60 + minute
            end = start + duration
            
            # Check if the time slot is within working hours
            if not (9 * 60 <= start < 17 * 60 and 9 * 60 <= end < 17 * 60):
                continue
            
            # Check if both are available
            if is_available(start, end, 'Gary') and is_available(start, end, 'David'):
                print(f"{start // 60:02d}:{start % 60:02d}-{end // 60:02d}:{end % 60:02d} Monday")
                return f"{start // 60:02d}:{start % 60:02d}-{end // 60:02d} Monday"
    
    # If no slot is found, return an error message
    return "No available time found."

# Run the function to find the meeting time
find_meeting_time()