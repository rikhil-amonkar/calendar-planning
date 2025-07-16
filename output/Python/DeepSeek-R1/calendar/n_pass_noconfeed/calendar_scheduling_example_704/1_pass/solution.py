work_start = 540   # 9:00 in minutes (since midnight)
work_end = 1020    # 17:00

# Samuel's busy times for each day in half-open intervals [start, end)
samuel_busy = {
    'Monday': [
        (630, 660),   # 10:30-11:00
        (720, 750),   # 12:00-12:30
        (780, 900),   # 13:00-15:00
        (930, 990)    # 15:30-16:30
    ],
    'Tuesday': [
        (540, 720),   # 9:00-12:00
        (840, 930),   # 14:00-15:30
        (990, 1020)   # 16:30-17:00
    ],
    'Wednesday': [
        (630, 660),   # 10:30-11:00
        (690, 720),   # 11:30-12:00
        (750, 780),   # 12:30-13:00
        (840, 870),   # 14:00-14:30
        (900, 960)    # 15:00-16:00
    ]
}

# We'll iterate over days in the given order
days = ['Monday', 'Tuesday', 'Wednesday']

result_day = None
result_start = None
result_end = None

for day in days:
    busy_intervals = samuel_busy[day]
    # If there are no busy intervals, the entire day is free
    if not busy_intervals:
        # Take the earliest 30 minutes in the work hours
        result_day = day
        result_start = work_start
        result_end = work_start + 30
        break
    
    # Sort by start time
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    merged = []
    start_curr, end_curr = sorted_busy[0]
    for i in range(1, len(sorted_busy)):
        s, e = sorted_busy[i]
        if s < end_curr:
            if e > end_curr:
                end_curr = e
        else:
            merged.append((start_curr, end_curr))
            start_curr, end_curr = s, e
    merged.append((start_curr, end_curr))
    
    # Now compute free slots in the work hours
    free_slots = []
    # Before the first meeting
    if merged[0][0] > work_start:
        free_slots.append((work_start, merged[0][0]))
    
    # Between meetings
    for i in range(1, len(merged)):
        prev_end = merged[i-1][1]
        curr_start = merged[i][0]
        if curr_start > prev_end:
            free_slots.append((prev_end, curr_start))
    
    # After the last meeting
    if merged[-1][1] < work_end:
        free_slots.append((merged[-1][1], work_end))
    
    # Check free_slots for a 30-minute slot
    found = False
    for slot in free_slots:
        start_slot, end_slot = slot
        duration = end_slot - start_slot
        if duration >= 30:
            result_day = day
            result_start = start_slot
            result_end = start_slot + 30
            found = True
            break
    
    if found:
        break

# Format the output
# Convert start and end minutes to HH:MM for the four numbers
start_hour = result_start // 60
start_minute = result_start % 60
end_hour = result_end // 60
end_minute = result_end % 60

# Format as two-digit strings
time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"

# Output the day and time string
print(result_day)
print(time_str)