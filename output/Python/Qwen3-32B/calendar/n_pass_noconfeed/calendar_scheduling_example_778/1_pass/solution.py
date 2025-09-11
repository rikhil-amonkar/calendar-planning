def get_available_times(blocked, start_day, end_day):
    blocked_sorted = sorted(blocked, key=lambda x: x[0])
    available = []
    prev_end = start_day
    for start, end in blocked_sorted:
        if start > prev_end:
            available.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < end_day:
        available.append((prev_end, end_day))
    return available

susan_blocked = {
    'Monday': [(12 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60)],
    'Tuesday': [(11 * 60 + 30, 12 * 60)],
    'Wednesday': [(9 * 60 + 30, 10 * 60 + 30), (14 * 60, 14 * 60 + 30), (15 * 60 + 30, 16 * 60 + 30)],
}

sandra_blocked = {
    'Monday': [(9 * 60, 13 * 60), (14 * 60, 15 * 60), (16 * 60, 16 * 60 + 30)],
    'Tuesday': [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60 + 30),
               (14 * 60, 14 * 60 + 30), (16 * 60, 17 * 60)],
    'Wednesday': [(9 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60, 17 * 60)],
}

days = ['Monday', 'Wednesday', 'Tuesday']

for day in days:
    # Compute Susan's available times
    susan_start_day = 540
    susan_end_day = 1020
    susan_blocked_day = susan_blocked.get(day, [])
    susan_available = get_available_times(susan_blocked_day, susan_start_day, susan_end_day)
    
    # Compute Sandra's available times
    if day == 'Monday':
        sandra_end_day = 960
    else:
        sandra_end_day = 1020
    sandra_start_day = 540
    sandra_blocked_day = sandra_blocked.get(day, [])
    sandra_available = get_available_times(sandra_blocked_day, sandra_start_day, sandra_end_day)
    
    # Check for overlapping intervals
    for susan_slot in susan_available:
        for sandra_slot in sandra_available:
            overlap_start = max(susan_slot[0], sandra_slot[0])
            overlap_end = min(susan_slot[1], sandra_slot[1])
            if overlap_end - overlap_start >= 30:
                # Found a valid slot, output the first 30-minute window
                start_time = overlap_start
                end_time = start_time + 30
                start_h = start_time // 60
                start_m = start_time % 60
                end_h = end_time // 60
                end_m = end_time % 60
                time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
                print(f"{time_str} {day}")
                exit()