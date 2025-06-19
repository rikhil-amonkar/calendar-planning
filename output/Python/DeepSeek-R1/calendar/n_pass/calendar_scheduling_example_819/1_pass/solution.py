work_start_minutes = 9 * 60  # 540 minutes (9:00)
work_end_minutes = 17 * 60   # 1020 minutes (17:00)

# Ruth's busy intervals in minutes for each day
ruth_busy = {
    'Monday': [[work_start_minutes, work_end_minutes]],
    'Tuesday': [[work_start_minutes, work_end_minutes]],
    'Wednesday': [[work_start_minutes, work_end_minutes]],
    'Thursday': [
        [540, 660],   # 9:00 to 11:00
        [690, 870],   # 11:30 to 14:30
        [900, 1020]   # 15:00 to 17:00
    ]
}

meeting_duration = 30  # minutes
days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
found = False
result_day = None
result_start_minutes = None
result_end_minutes = None

for day in days:
    busy_intervals = ruth_busy[day]
    free_intervals = []
    current_start = work_start_minutes
    
    # Sort busy intervals by start time
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    
    for interval in sorted_busy:
        if current_start < interval[0]:
            free_intervals.append([current_start, interval[0]])
        current_start = max(current_start, interval[1])
    if current_start < work_end_minutes:
        free_intervals.append([current_start, work_end_minutes])
    
    for interval in free_intervals:
        start_min = interval[0]
        end_min = interval[1]
        duration_available = end_min - start_min
        if duration_available >= meeting_duration:
            if day == 'Thursday':
                if start_min < 690:  # 11:30 in minutes
                    continue
            result_day = day
            result_start_minutes = start_min
            result_end_minutes = start_min + meeting_duration
            found = True
            break
    if found:
        break

if found:
    start_hour = result_start_minutes // 60
    start_minute = result_start_minutes % 60
    end_hour = result_end_minutes // 60
    end_minute = result_end_minutes % 60
    
    start_str = f"{start_hour}:{start_minute:02d}"
    end_str = f"{end_hour}:{end_minute:02d}"
    time_range_str = f"{{{start_str}:{end_str}}}"
    
    print(result_day)
    print(time_range_str)
else:
    print("No suitable time found")