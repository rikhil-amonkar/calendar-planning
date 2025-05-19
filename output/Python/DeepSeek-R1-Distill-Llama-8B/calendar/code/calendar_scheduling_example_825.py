def find_meeting_time():
    # Define the working hours
    work_hours = [(9, 17), (9, 17), (9, 17), (9, 17)]  # Monday, Tuesday, Wednesday, Thursday
    # Meeting duration
    duration = 1
    
    # Available days based on Philip's constraints
    available_days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    
    # Check each day for possible meeting times
    for day in available_days:
        # Convert day to numerical value for easier comparison
        day_num = {'Monday': 0, 'Tuesday': 1, 'Wednesday': 2, 'Thursday': 3}[day]
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
    # Check Laura's schedule
    blocked_times = {
        0: [(10*60 + 30, 11*60), (12*60 + 30, 13*60), (14*60 + 30, 15*60), (16*60, 17*60)],
        1: [(9*60 + 30, 10*60), (11*60, 11*60 + 30), (13*60, 13*60 + 30), (14*60 + 30, 15*60), (16*60, 17*60)],
        2: [(11*60 + 30, 12*60), (12*60 + 30, 13*60), (15*60 + 30, 16*60), (17*60, 18*60)],  # Wednesday is blocked for Philip
        3: [(10*60 + 30, 11*60), (12*60, 13*60 + 30), (15*60, 15*60 + 30), (16*60, 16*60 + 30)]
    }
    
    if day_num in blocked_times:
        for start, end in blocked_times[day_num]:
            if start <= slot[0] < end:
                return False
    
    # Check Philip's schedule
    blocked_philip = {
        0: [(9*60, 17*60)],  # Monday is fully blocked
        1: [(9*60 + 30, 10*60), (11*60 + 30, 12*60), (13*60, 13*60 + 30), (14*60, 14*60 + 30), (15*60, 16*60 + 30)],
        2: [(9*60, 10*60), (11*60, 12*60), (12*60 + 30, 16*60), (16*60 + 30, 17*60)],
        3: [(9*60, 10*60 + 30), (11*60, 12*60 + 30), (13*60, 17*60)]
    }
    
    if day_num in blocked_philip:
        for start, end in blocked_philip[day_num]:
            if start <= slot[0] < end:
                return False
    
    return True

# Run the function to find the meeting time
find_meeting_time()