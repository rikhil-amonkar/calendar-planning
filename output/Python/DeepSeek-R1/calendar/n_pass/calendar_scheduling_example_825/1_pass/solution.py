work_start_min = 540  # 9:00 in minutes
work_end_min = 1020   # 17:00 in minutes

# Define busy intervals as half-open [start, end) in minutes
laura_busy = {
    'Monday': [(630, 660), (750, 780), (870, 930), (960, 1020)],
    'Tuesday': [(570, 600), (660, 690), (780, 810), (870, 900), (960, 1020)],
    'Wednesday': [(690, 720), (750, 780), (930, 990)],
    'Thursday': [(630, 660), (720, 810), (900, 930), (960, 990)]
}

philip_busy = {
    'Monday': [(540, 1020)],
    'Tuesday': [(540, 660), (690, 720), (780, 810), (840, 870), (900, 990)],
    'Wednesday': [(540, 600), (660, 720), (750, 960), (990, 1020)],
    'Thursday': [(540, 630), (660, 750), (780, 1020)]
}

days_to_check = ['Monday', 'Tuesday', 'Thursday']  # Skip Wednesday

for day in days_to_check:
    # Combine busy intervals for both participants
    all_busy = laura_busy[day] + philip_busy[day]
    all_busy.sort(key=lambda x: x[0])
    
    # Merge intervals
    merged = []
    for s, e in all_busy:
        if not merged:
            merged.append((s, e))
        else:
            last_s, last_e = merged[-1]
            if s <= last_e:
                merged[-1] = (last_s, max(last_e, e))
            else:
                merged.append((s, e))
    
    # Find free intervals
    free = []
    current = work_start_min
    for s, e in merged:
        if current < s:
            free.append((current, s))
        current = e
    if current < work_end_min:
        free.append((current, work_end_min))
    
    # Check for a free interval of at least 60 minutes
    for fs, fe in free:
        if fe - fs >= 60:
            meeting_start = fs
            meeting_end = fs + 60
            # Format meeting times
            start_hour = meeting_start // 60
            start_minute = meeting_start % 60
            end_hour = meeting_end // 60
            end_minute = meeting_end % 60
            time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
            print(day)
            print(time_str)
            exit()

# If no solution found, but problem states there is one
print("No suitable time found")