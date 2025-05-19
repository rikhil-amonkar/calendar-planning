def convert_time(h, m):
    return h * 60 + m

def find_meeting_time():
    work_start = convert_time(9, 0)
    work_end = convert_time(17, 0)
    duration = 30
    day = "Monday"
    
    # Convert all busy times to minutes
    busy = {
        'Kathleen': [(convert_time(14,30), convert_time(15,30))],
        'Carolyn': [(convert_time(12,0), convert_time(12,30)), (convert_time(13,0), convert_time(13,30))],
        'Cheryl': [(convert_time(9,0), convert_time(9,30)), (convert_time(10,0), convert_time(11,30)), 
                  (convert_time(12,30), convert_time(13,30)), (convert_time(14,0), convert_time(17,0))],
        'Virginia': [(convert_time(9,30), convert_time(11,30)), (convert_time(12,0), convert_time(12,30)), 
                    (convert_time(13,0), convert_time(13,30)), (convert_time(14,30), convert_time(15,30)),
                    (convert_time(16,0), convert_time(17,0))],
        'Angela': [(convert_time(9,30), convert_time(10,0)), (convert_time(10,30), convert_time(11,30)),
                  (convert_time(12,0), convert_time(12,30)), (convert_time(13,0), convert_time(13,30)),
                  (convert_time(14,0), convert_time(16,30))]
    }
    
    # Combine all busy intervals and Roger's preference
    all_busy = []
    for intervals in busy.values():
        all_busy.extend(intervals)
    all_busy.append((work_start, convert_time(12,30)))  # Roger's preference
    
    # Sort all intervals and merge overlapping
    sorted_intervals = sorted(all_busy)
    merged = []
    for start, end in sorted_intervals:
        if not merged or merged[-1][1] < start:
            merged.append([start, end])
        else:
            merged[-1][1] = max(merged[-1][1], end)
    
    # Check gaps between merged intervals and work hours
    possible_start = work_start
    for start, end in merged:
        if possible_start + duration <= start:
            final_start = possible_start
            final_end = final_start + duration
            return (final_start, final_end, day)
        possible_start = max(possible_start, end)
    
    # Check after last interval
    if possible_start + duration <= work_end:
        final_start = possible_start
        final_end = final_start + duration
        return (final_start, final_end, day)
    
    return None

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

result = find_meeting_time()
if result:
    start, end, day = result
    start_str = format_time(start)
    end_str = format_time(end)
    print(f"{day}:{start_str}:{end_str}")
else:
    print("No suitable time found")