def find_meeting_time():
    # Define work hours and days to consider
    work_hours = (9, 17)  # 9:00 to 17:00
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Define existing schedules for Arthur and Michael
    arthur_schedule = {
        'Monday': [(11, 0, 11, 30), (13, 30, 14, 0), (15, 0, 15, 30)],
        'Tuesday': [(13, 0, 13, 30), (16, 0, 16, 30)],
        'Wednesday': [(10, 0, 10, 30), (11, 0, 11, 30), (12, 0, 12, 30), (14, 0, 14, 30), (16, 0, 16, 30)]
    }
    
    michael_schedule = {
        'Monday': [(9, 0, 12, 0), (12, 30, 13, 0), (14, 0, 14, 30), (15, 0, 17, 0)],
        'Tuesday': [(9, 30, 11, 30), (12, 0, 13, 30), (14, 0, 15, 30)],
        'Wednesday': [(10, 0, 12, 30), (13, 0, 13, 30)]
    }
    
    # Arthur cannot meet on Tuesday
    days_to_check = [day for day in days if day != 'Tuesday']
    
    # Iterate through each day to find the earliest available slot
    for day in days_to_check:
        # Combine and sort all meetings for both participants on the current day
        all_meetings = []
        for meeting in arthur_schedule.get(day, []):
            all_meetings.append((meeting[0] * 60 + meeting[1], meeting[2] * 60 + meeting[3]))
        for meeting in michael_schedule.get(day, []):
            all_meetings.append((meeting[0] * 60 + meeting[1], meeting[2] * 60 + meeting[3]))
        
        # Sort meetings by start time
        all_meetings.sort()
        
        # Check available slots between work hours
        prev_end = work_hours[0] * 60  # Start of work day in minutes
        
        for meeting in all_meetings:
            start, end = meeting
            if start > prev_end:
                # Check if the gap is at least 30 minutes
                if start - prev_end >= 30:
                    # Found a suitable slot
                    slot_start = prev_end
                    slot_end = slot_start + 30
                    # Convert back to hours and minutes
                    start_h = slot_start // 60
                    start_m = slot_start % 60
                    end_h = slot_end // 60
                    end_m = slot_end % 60
                    return day, f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
            # Update prev_end to the end of the current meeting
            prev_end = max(prev_end, end)
        
        # Check after the last meeting until end of work day
        if prev_end < work_hours[1] * 60:
            if (work_hours[1] * 60) - prev_end >= 30:
                slot_start = prev_end
                slot_end = slot_start + 30
                start_h = slot_start // 60
                start_m = slot_start % 60
                end_h = slot_end // 60
                end_m = slot_end % 60
                return day, f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    
    return None, None

# Execute the function and print the result
day, time_slot = find_meeting_time()
if day and time_slot:
    print(f"{day}: {time_slot}")
else:
    print("No suitable time slot found.")