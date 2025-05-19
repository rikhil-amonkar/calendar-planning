def find_meeting_time():
    # Define work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    
    # Define participants' busy times in minutes since midnight
    busy_times = {
        'Christine': [(570, 630), (720, 750), (780, 810), (870, 900), (960, 990)],
        'Bobby': [(720, 750), (870, 900)],
        'Elizabeth': [(540, 570), (690, 780), (810, 840), (900, 930), (960, 1020)],
        'Tyler': [(540, 660), (720, 750), (780, 810), (930, 960), (990, 1020)],
        'Edward': [(540, 570), (600, 660), (690, 840), (870, 930), (960, 1020)],
    }
    
    # Janice's preference: not after 13:00 (780 minutes)
    janice_pref_end = 13 * 60
    
    # Collect all busy times and Janice's preference
    all_busy = []
    for person in busy_times:
        all_busy.extend(busy_times[person])
    all_busy.sort()
    
    # Merge overlapping or adjacent busy times
    merged_busy = []
    for start, end in all_busy:
        if not merged_busy:
            merged_busy.append((start, end))
        else:
            last_start, last_end = merged_busy[-1]
            if start <= last_end:
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged_busy[-1] = (new_start, new_end)
            else:
                merged_busy.append((start, end))
    
    # Add Janice's preference as a "busy" time after 13:00
    merged_busy.append((janice_pref_end, work_end))
    merged_busy.sort()
    
    # Find the earliest available 30-minute slot
    prev_end = work_start
    meeting_duration = 30
    
    for start, end in merged_busy:
        if start - prev_end >= meeting_duration:
            # Found a slot
            meeting_start = prev_end
            meeting_end = meeting_start + meeting_duration
            # Format the time as HH:MM:HH:MM
            start_hh = meeting_start // 60
            start_mm = meeting_start % 60
            end_hh = meeting_end // 60
            end_mm = meeting_end % 60
            time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
            return time_str, "Monday"
        prev_end = max(prev_end, end)
    
    return None, None

time_range, day = find_meeting_time()
print(f"{{{time_range}}} {day}")