def find_meeting_time():
    # Define work hours and days to check
    work_hours = (9, 17)
    days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Define blocked time ranges in minutes since 9:00 (540 minutes)
    martha_blocked = {
        'Monday': [(16*60, 17*60)],
        'Tuesday': [(15*60, 15*60+30)],
        'Wednesday': [(10*60, 11*60), (14*60, 14*60+30)]
    }
    
    beverly_blocked = {
        'Monday': [(9*60, 13*60+30), (14*60, 17*60)],
        'Tuesday': [(9*60, 17*60)],
        'Wednesday': [(9*60+30, 15*60+30), (16*60+30, 17*60)]
    }
    
    # Check each day for available slots
    for day in days:
        # Convert work hours to minutes
        start = work_hours[0] * 60
        end = work_hours[1] * 60
        
        # Get blocked times for both participants
        m_blocks = martha_blocked.get(day, [])
        b_blocks = beverly_blocked.get(day, [])
        
        # Combine and sort all blocked times
        all_blocks = sorted(m_blocks + b_blocks, key=lambda x: x[0])
        
        # Find free intervals
        current_time = start
        free_slots = []
        
        for block in all_blocks:
            if block[0] > current_time:
                free_slots.append((current_time, block[0]))
            current_time = max(current_time, block[1])
        if current_time < end:
            free_slots.append((current_time, end))
        
        # Check for a 60-minute slot
        for slot in free_slots:
            slot_duration = slot[1] - slot[0]
            if slot_duration >= 60:
                # Found suitable slot
                start_time = slot[0]
                meeting_end = start_time + 60
                # Convert back to HH:MM format
                start_h = start_time // 60
                start_m = start_time % 60
                end_h = meeting_end // 60
                end_m = meeting_end % 60
                return (
                    day,
                    f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
                )
    
    return None

result = find_meeting_time()
if result:
    print(f"{result[0]} {result[1]}")
else:
    print("No suitable time found")