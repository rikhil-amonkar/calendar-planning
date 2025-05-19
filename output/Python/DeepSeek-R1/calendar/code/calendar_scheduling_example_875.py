def find_meeting_time():
    # Define work hours and days
    work_hours = (9, 17)
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    
    # Define schedules in 24h format as (start_h, start_m, end_h, end_m)
    schedules = {
        'Natalie': {
            'Monday': [(9, 0, 9, 30), (10, 0, 12, 0), (12, 30, 13, 0), (14, 0, 14, 30), (15, 0, 16, 30)],
            'Tuesday': [(9, 0, 9, 30), (10, 0, 10, 30), (12, 30, 14, 0), (16, 0, 17, 0)],
            'Wednesday': [(11, 0, 11, 30), (16, 0, 16, 30)],
            'Thursday': [(10, 0, 11, 0), (11, 30, 15, 0), (15, 30, 16, 0), (16, 30, 17, 0)]
        },
        'William': {
            'Monday': [(9, 30, 11, 0), (11, 30, 17, 0)],
            'Tuesday': [(9, 0, 13, 0), (13, 30, 16, 0)],
            'Wednesday': [(9, 0, 12, 30), (13, 0, 14, 30), (15, 30, 16, 0), (16, 30, 17, 0)],
            'Thursday': [(9, 0, 10, 30), (11, 0, 11, 30), (12, 0, 12, 30), (13, 0, 14, 0), (15, 0, 17, 0)]
        }
    }

    # Convert schedules to minutes for easier comparison
    for day in days:
        for person in schedules:
            converted = []
            for block in schedules[person].get(day, []):
                start = block[0] * 60 + block[1]
                end = block[2] * 60 + block[3]
                converted.append((start, end))
            schedules[person][day] = converted

    # Check each day for available slot
    for day in days:
        # Get all busy blocks for both participants
        natalie_busy = schedules['Natalie'][day]
        william_busy = schedules['William'][day]
        
        # Create merged busy timeline (union of both schedules)
        merged_busy = []
        current_idx = 0
        all_blocks = sorted(natalie_busy + william_busy, key=lambda x: x[0])
        for block in all_blocks:
            if not merged_busy:
                merged_busy.append(block)
            else:
                last = merged_busy[-1]
                if block[0] <= last[1]:
                    merged_busy[-1] = (last[0], max(last[1], block[1]))
                else:
                    merged_busy.append(block)
        
        # Add work hours boundaries
        day_start = work_hours[0] * 60
        day_end = work_hours[1] * 60
        timeline = [(day_start, day_start)]  # Initial dummy entry
        
        if merged_busy:
            timeline.extend(merged_busy)
        else:
            # Entire day is free
            return f"{day}: {work_hours[0]:02d}:00-{work_hours[0]+1:02d}:00"
        
        # Find first gap of at least 60 minutes
        for i in range(1, len(timeline)):
            prev_end = timeline[i-1][1]
            curr_start = timeline[i][0]
            if curr_start - prev_end >= 60:
                # Found suitable gap
                start_h, start_m = divmod(prev_end, 60)
                end_h, end_m = divmod(prev_end + 60, 60)
                return f"{day}: {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}"
        
        # Check after last meeting
        last_end = timeline[-1][1]
        if day_end - last_end >= 60:
            start_h, start_m = divmod(last_end, 60)
            end_h, end_m = divmod(last_end + 60, 60)
            return f"{day}: {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}"

    return "No suitable time found"

# Execute and print result
print(find_meeting_time())