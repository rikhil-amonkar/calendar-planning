def find_meeting_time():
    # Define work hours and days to check
    work_start = 9 * 60
    work_end = 17 * 60
    days = ['Tuesday', 'Wednesday', 'Thursday']  # Monday excluded per Betty's constraint
    
    # Convert schedules to minutes since midnight
    betty_busy = {
        'Tuesday': [(9*60, 9*60+30), (11*60+30, 12*60), (12*60+30, 13*60), (13*60+30, 14*60), (16*60+30, 17*60)],
        'Wednesday': [(9*60+30, 10*60+30), (13*60, 13*60+30), (14*60, 14*60+30)],
        'Thursday': [(9*60+30, 10*60), (11*60+30, 12*60), (14*60, 14*60+30), (15*60, 15*60+30), (16*60+30, 17*60)]
    }
    
    scott_busy = {
        'Tuesday': [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 12*60), (12*60+30, 13*60+30), (14*60, 15*60), (16*60, 16*60+30)],
        'Wednesday': [(9*60+30, 12*60+30), (13*60, 13*60+30), (14*60, 14*60+30), (15*60, 15*60+30), (16*60, 16*60+30)],
        'Thursday': [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 12*60), (12*60+30, 13*60), (15*60, 16*60), (16*60+30, 17*60)]
    }

    # Check possible days with priority order
    for day in days:
        # Apply Betty's time constraints
        if day == 'Tuesday' or day == 'Thursday':
            min_start = 15 * 60  # 15:00
        else:
            min_start = work_start
        
        # Generate free slots for both participants
        slots = []
        current_start = max(work_start, min_start)
        
        # Combine and sort all busy times
        all_busy = sorted(betty_busy.get(day, []) + scott_busy.get(day, []), key=lambda x: x[0])
        
        for start, end in all_busy:
            if current_start < start:
                slots.append((current_start, start))
            current_start = max(current_start, end)
        if current_start < work_end:
            slots.append((current_start, work_end))
        
        # Find first 30-minute slot
        for slot_start, slot_end in slots:
            if slot_end - slot_start >= 30:
                meeting_start = slot_start
                # Adjust for Betty's Thursday constraint
                if day == 'Thursday' and meeting_start < 15 * 60:
                    continue
                return (
                    day,
                    f"{meeting_start//60:02d}:{meeting_start%60:02d}:"
                    f"{(meeting_start+30)//60:02d}:{(meeting_start+30)%60:02d}"
                )
    
    # Fallback to Wednesday 9:00 if no other slots (shouldn't reach here per problem statement)
    return ('Wednesday', "09:00:09:30")

day, time = find_meeting_time()
print(f"{day} {time}")