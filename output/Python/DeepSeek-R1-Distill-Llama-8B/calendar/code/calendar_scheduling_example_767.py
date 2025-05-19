def find_meeting_time():
    # Define the working hours
    work_hours = [(9, 17), (9, 17), (9, 17)]  # Monday, Tuesday, Wednesday
    # Meeting duration
    duration = 1
    
    # Available days based on the participants' constraints
    available_days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Check each day for possible meeting times
    for day in available_days:
        # Convert day to numerical value for easier comparison
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
            # Check if the time slot is within working hours
            if 9 * 60 <= time_start < 17 * 60 and 9 * 60 <= time_end < 17 * 60:
                # Check if the slot is available for both participants
                if is_available(day_num, slot):
                    available_slots.append(slot)
        
        # Find the first available slot that works for both participants
        for slot in available_slots:
            time_start, time_end = slot
            print(f"{time_start // 60:02d}:{time_start % 60:02d}-{time_end // 60:02d}:{time_end % 60:02d} {day}")
            return f"{time_start // 60:02d}:{time_start % 60:02d}-{time_end // 60:02d} {day}"
    
    # If no slot is found, return an error message
    return "No available time found."

def is_available(day_num, slot):
    # Check Martha's schedule
    blocked_martha = {
        0: [(16 * 60, 17 * 60)],  # Monday
        1: [(15 * 60, 15 * 60 + 30)],  # Tuesday
        2: [(10 * 60, 11 * 60), (14 * 60, 14 * 60 + 30)]  # Wednesday
    }
    
    if day_num in blocked_martha:
        for start, end in blocked_martha[day_num]:
            if start <= slot[0] < end:
                return False
    
    # Check Beverly's schedule
    blocked_beverly = {
        0: [(9 * 60, 13 * 60 + 30), (14 * 60, 17 * 60)],  # Monday
        1: [(9 * 60, 17 * 60)],  # Tuesday
        2: [(9 * 60 + 30, 15 * 60 + 30), (16 * 60 + 30, 17 * 60)]  # Wednesday
    }
    
    if day_num in blocked_beverly:
        for start, end in blocked_beverly[day_num]:
            if start <= slot[0] < end:
                return False
    
    return True

# Run the function to find the meeting time
find_meeting_time()