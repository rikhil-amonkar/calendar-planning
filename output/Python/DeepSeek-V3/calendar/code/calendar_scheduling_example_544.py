def find_meeting_time():
    # Participants' constraints
    work_hours_start = 9 * 60  # 9:00 in minutes
    work_hours_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30       # minutes
    
    # Albert's busy times in minutes since 9:00
    albert_busy = [
        (9 * 60, 10 * 60),      # 9:00-10:00
        (10 * 60 + 30, 12 * 60), # 10:30-12:00
        (15 * 60, 16 * 60 + 30)  # 15:00-16:30
    ]
    
    # Albert cannot meet after 11:00
    albert_cutoff = 11 * 60
    
    # Deborah is free all day, so only Albert's schedule matters
    
    # Find all possible slots
    possible_slots = []
    
    # Check before Albert's first busy block
    if work_hours_start + meeting_duration <= albert_busy[0][0]:
        possible_slots.append((work_hours_start, work_hours_start + meeting_duration))
    
    # Check between Albert's busy blocks
    for i in range(len(albert_busy) - 1):
        end_previous = albert_busy[i][1]
        start_next = albert_busy[i + 1][0]
        if end_previous + meeting_duration <= start_next:
            possible_slots.append((end_previous, end_previous + meeting_duration))
    
    # Check after Albert's last busy block but before his cutoff
    end_last_busy = albert_busy[-1][1]
    if end_last_busy + meeting_duration <= albert_cutoff:
        possible_slots.append((end_last_busy, end_last_busy + meeting_duration))
    
    # Also check if there's time before cutoff but not covered by busy blocks
    # For example, between 12:00 and 15:00, but Albert cannot meet after 11:00
    # So this is not applicable here
    
    # Select the earliest possible slot
    if possible_slots:
        chosen_slot = possible_slots[0]
        start_time = chosen_slot[0]
        end_time = chosen_slot[1]
        
        # Convert minutes back to HH:MM format
        start_hh = start_time // 60
        start_mm = start_time % 60
        end_hh = end_time // 60
        end_mm = end_time % 60
        
        # Format as HH:MM:HH:MM
        time_range = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
        day = "Monday"
        
        print(f"{time_range}")
        print(f"{day}")
    else:
        print("No suitable time found.")

find_meeting_time()