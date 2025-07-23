def find_meeting_time():
    # Define work hours and days
    work_hours = (9, 17)  # 9:00 to 17:00
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    
    # Define participants' constraints
    julie_constraints = {
        'Monday': [],
        'Tuesday': [],
        'Wednesday': [],
        'Thursday': [('9:00', '11:30')]  # Avoid before 11:30 on Thursday
    }
    
    ruth_busy = {
        'Monday': [('9:00', '17:00')],
        'Tuesday': [('9:00', '17:00')],
        'Wednesday': [('9:00', '17:00')],
        'Thursday': [('9:00', '11:00'), ('11:30', '14:30'), ('15:00', '17:00')]
    }
    
    meeting_duration = 30  # minutes
    
    # Iterate through each day to find a suitable time
    for day in days:
        # Merge Julie's and Ruth's constraints for the day
        constraints = []
        
        # Add Julie's constraints
        for time_range in julie_constraints[day]:
            start, end = time_range
            start_h, start_m = map(int, start.split(':'))
            end_h, end_m = map(int, end.split(':'))
            constraints.append((start_h * 60 + start_m, end_h * 60 + end_m))
        
        # Add Ruth's busy times
        for time_range in ruth_busy[day]:
            start, end = time_range
            start_h, start_m = map(int, start.split(':'))
            end_h, end_m = map(int, end.split(':'))
            constraints.append((start_h * 60 + start_m, end_h * 60 + end_m))
        
        # Sort constraints by start time
        constraints.sort()
        
        # Find available slots between work hours
        available_slots = []
        prev_end = work_hours[0] * 60  # Start of work day in minutes
        
        for start, end in constraints:
            if start > prev_end:
                available_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        # Check after last constraint
        if prev_end < work_hours[1] * 60:
            available_slots.append((prev_end, work_hours[1] * 60))
        
        # Check for a slot that can fit the meeting
        for slot in available_slots:
            slot_start, slot_end = slot
            if slot_end - slot_start >= meeting_duration:
                # Found a suitable slot
                meeting_start = slot_start
                meeting_end = meeting_start + meeting_duration
                
                # Convert back to HH:MM format
                start_h = meeting_start // 60
                start_m = meeting_start % 60
                end_h = meeting_end // 60
                end_m = meeting_end % 60
                
                # Format the output
                time_range = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
                return day, time_range
    
    return None, None

# Execute the function and print the result
day, time_range = find_meeting_time()
print(f"{day}: {time_range}")