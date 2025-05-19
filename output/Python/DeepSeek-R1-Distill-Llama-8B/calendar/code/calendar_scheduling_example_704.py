def find_meeting_time():
    # Define the working hours
    work_hours = [(9, 17), (9, 17), (9, 17)]  # Monday, Tuesday, Wednesday
    # Meeting duration
    duration = 30  # 30 minutes
    
    # Blocked times for Samuel
    blocked_times = {
        'Monday': [(10 * 60 + 30, 11 * 60), (12 * 60, 12 * 60 + 30), (13 * 60, 15 * 60), 
                  (15 * 60 + 30, 16 * 60 + 30)],
        'Tuesday': [(9 * 60, 12 * 60), (14 * 60, 15 * 60 + 30), (16 * 60, 17 * 60)],
        'Wednesday': [(10 * 60, 11 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), 
                     (14 * 60, 14 * 60 + 30), (15 * 60, 16 * 60)]
    }
    
    # Function to check availability
    def is_available(start, end, day):
        return not any(block_start <= start < block_end for block_start, block_end in blocked_times.get(day, []))
    
    # Check each day for possible meeting times
    for day in ['Monday', 'Tuesday', 'Wednesday']:
        day_num = {'Monday': 0, 'Tuesday': 1, 'Wednesday': 2}[day]
        start_time = 9 * 60
        end_time = 17 * 60
        
        # Create a list of all time slots for the day
        time_slots = []
        for hour in range(9, 17):
            for minute in range(0, 60):
                time_slots.append((hour * 60 + minute, hour * 60 + minute + duration))
        
        # Filter time slots based on blocked times
        available_slots = []
        for slot in time_slots:
            time_start, time_end = slot
            if 9 * 60 <= time_start < 17 * 60 and 9 * 60 <= time_end < 17 * 60:
                if is_available(time_start, time_end, day):
                    available_slots.append(slot)
        
        # Find the first available slot that works for both participants
        for slot in available_slots:
            time_start, time_end = slot
            print(f"{time_start // 60:02d}:{time_start % 60:02d}-{time_end // 60:02d}:{time_end % 60:02d} {day}")
            return f"{time_start // 60:02d}:{time_start % 60:02d}-{time_end // 60:02d} {day}"
    
    # If no slot is found, return an error message
    return "No available time found."

# Run the function to find the meeting time
find_meeting_time()