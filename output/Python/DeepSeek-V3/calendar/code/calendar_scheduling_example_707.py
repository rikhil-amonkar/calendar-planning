def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Define constraints and busy times for each participant
    ryan_busy = {
        'Monday': [(9*60 + 30, 10*60), (11*60, 12*60), (13*60, 13*60 + 30), (15*60 + 30, 16*60)],
        'Tuesday': [(11*60 + 30, 12*60 + 30), (15*60 + 30, 16*60)],
        'Wednesday': [(12*60, 13*60), (15*60 + 30, 16*60), (16*60 + 30, 17*60)]
    }
    
    adam_busy = {
        'Monday': [(9*60, 10*60 + 30), (11*60, 13*60 + 30), (14*60, 16*60), (16*60 + 30, 17*60)],
        'Tuesday': [(9*60, 10*60), (10*60 + 30, 15*60 + 30), (16*60, 17*60)],
        'Wednesday': [(9*60, 9*60 + 30), (10*60, 11*60), (11*60 + 30, 14*60 + 30), (15*60, 15*60 + 30), (16*60, 16*60 + 30)]
    }
    
    # Apply constraints: Ryan cannot meet on Wednesday, Adam avoids Monday before 14:30
    days_to_check = ['Monday', 'Tuesday']  # Wednesday is excluded due to Ryan's constraint
    
    meeting_duration = 30  # minutes
    
    for day in days_to_check:
        # Combine and sort busy times for both participants
        combined_busy = ryan_busy[day] + adam_busy[day]
        combined_busy.sort()
        
        # Merge overlapping or adjacent busy intervals
        merged_busy = []
        for start, end in combined_busy:
            if not merged_busy:
                merged_busy.append((start, end))
            else:
                last_start, last_end = merged_busy[-1]
                if start <= last_end:
                    # Overlapping or adjacent, merge them
                    new_start = min(last_start, start)
                    new_end = max(last_end, end)
                    merged_busy[-1] = (new_start, new_end)
                else:
                    merged_busy.append((start, end))
        
        # Check available slots
        prev_end = work_start
        for start, end in merged_busy:
            if start > prev_end:
                # Found a potential slot
                slot_start = prev_end
                slot_end = start
                if slot_end - slot_start >= meeting_duration:
                    # Check Adam's Monday before 14:30 constraint
                    if day == 'Monday' and slot_start < 14*60 + 30:
                        continue  # Skip this slot
                    # Found a valid slot
                    meeting_start = slot_start
                    meeting_end = meeting_start + meeting_duration
                    # Format the time as HH:MM:HH:MM
                    start_hh = meeting_start // 60
                    start_mm = meeting_start % 60
                    end_hh = meeting_end // 60
                    end_mm = meeting_end % 60
                    time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
                    return day, time_str
            prev_end = max(prev_end, end)
        
        # Check after the last busy interval
        if work_end - prev_end >= meeting_duration:
            # Check Adam's Monday before 14:30 constraint
            if day == 'Monday' and prev_end < 14*60 + 30:
                continue  # Skip this slot
            meeting_start = prev_end
            meeting_end = meeting_start + meeting_duration
            # Format the time as HH:MM:HH:MM
            start_hh = meeting_start // 60
            start_mm = meeting_start % 60
            end_hh = meeting_end // 60
            end_mm = meeting_end % 60
            time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
            return day, time_str
    
    return None, None

day, time_slot = find_meeting_time()
print(f"{day}: {time_slot}")