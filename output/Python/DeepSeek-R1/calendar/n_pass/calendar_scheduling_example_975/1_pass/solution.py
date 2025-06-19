days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']

# Nicole's busy times
nicole_busy = {
    'Tuesday': [('16:00', '16:30')],
    'Wednesday': [('15:00', '15:30')],
    'Friday': [('12:00', '12:30'), ('15:30', '16:00')]
}

# Daniel's busy times
daniel_busy = {
    'Monday': [('9:00', '12:30'), ('13:00', '13:30'), ('14:00', '16:30')],
    'Tuesday': [('9:00', '10:30'), ('11:30', '12:30'), ('13:00', '13:30'), ('15:00', '16:00'), ('16:30', '17:00')],
    'Wednesday': [('9:00', '10:00'), ('11:00', '12:30'), ('13:00', '13:30'), ('14:00', '14:30'), ('16:30', '17:00')],
    'Thursday': [('11:00', '12:00'), ('13:00', '14:00'), ('15:00', '15:30')],
    'Friday': [('10:00', '11:00'), ('11:30', '12:00'), ('12:30', '14:30'), ('15:00', '15:30'), ('16:00', '16:30')]
}

def time_to_slot(time_str):
    """Convert time string to slot index (0-based, relative to 9:00)"""
    hr, min = map(int, time_str.split(':'))
    total_min = (hr - 9) * 60 + min
    return total_min // 30

# Iterate over days in order
for day in days:
    # Initialize free arrays (True means free)
    nicole_free = [True] * 16
    daniel_free = [True] * 16
    
    # Mark Nicole's busy slots for this day
    if day in nicole_busy:
        for interval in nicole_busy[day]:
            start, end = interval
            start_slot = time_to_slot(start)
            end_slot = time_to_slot(end)
            for slot in range(start_slot, end_slot):
                if slot < 16:
                    nicole_free[slot] = False
    
    # Mark Daniel's busy slots for this day
    if day in daniel_busy:
        for interval in daniel_busy[day]:
            start, end = interval
            start_slot = time_to_slot(start)
            end_slot = time_to_slot(end)
            for slot in range(start_slot, end_slot):
                if slot < 16:
                    daniel_free[slot] = False
    
    # Combine: slot is free only if both are free
    group_free = [nicole_free[i] and daniel_free[i] for i in range(16)]
    
    # Find two consecutive free slots (1-hour meeting)
    for i in range(0, 15):
        if group_free[i] and group_free[i+1]:
            # Calculate start time (from slot index)
            total_minutes_start = 9 * 60 + i * 30
            start_hr = total_minutes_start // 60
            start_min = total_minutes_start % 60
            
            # Calculate end time (start time + 60 minutes)
            total_minutes_end = total_minutes_start + 60
            end_hr = total_minutes_end // 60
            end_min = total_minutes_end % 60
            
            # Format time string (HH:MM:HH:MM)
            time_str = f"{start_hr}:{start_min:02d}:{end_hr}:{end_min:02d}"
            
            # Output day and time string
            print(day)
            print(time_str)
            exit()

# If no solution found (shouldn't happen per problem)
print("No suitable time found")