def find_meeting_time():
    work_start = 9 * 60  # 540 minutes (9:00)
    work_end = 17 * 60   # 1020 minutes (17:00)
    
    # Patrick's busy intervals in minutes since midnight
    busy = [
        (540, 570),  # 9:00–9:30
        (630, 720),  # 10:30–12:00
        (750, 810),  # 12:30–13:30
        (840, 870),  # 14:00–14:30
        (900, 990)   # 15:00–16:30
    ]
    
    # Sort busy intervals by start time
    busy.sort()
    
    # Check the time before the first busy interval
    if busy[0][0] - work_start >= 30:
        return (work_start, work_start + 30)
    
    # Check gaps between busy intervals
    for i in range(1, len(busy)):
        prev_end = busy[i-1][1]
        curr_start = busy[i][0]
        gap_start = prev_end
        gap_end = curr_start
        
        if gap_end - gap_start >= 30:
            return (gap_start, gap_start + 30)
    
    # Check the time after the last busy interval
    last_end = busy[-1][1]
    if work_end - last_end >= 30:
        return (last_end, last_end + 30)
    
    # If no 30-minute slot found (should not happen in this case)
    return None

# Convert minutes back to HH:MM format for display
meeting = find_meeting_time()
if meeting:
    start = meeting[0]
    end = meeting[1]
    print(f"Meeting scheduled from {start//60:02d}:{start%60:02d} to {end//60:02d}:{end%60:02d}")
else:
    print("No available time slot found.")
    