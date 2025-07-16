def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return (hour - 9) * 60 + minute

def minutes_to_time(minutes):
    total_minutes = minutes
    hour = 9 + total_minutes // 60
    minute = total_minutes % 60
    return f"{hour:02d}:{minute:02d}"

# Define the busy times for Laura and Philip
laura_busy = {
    'Monday': [('10:30','11:00'), ('12:30','13:00'), ('14:30','15:30'), ('16:00','17:00')],
    'Tuesday': [('9:30','10:00'), ('11:00','11:30'), ('13:00','13:30'), ('14:30','15:00'), ('16:00','17:00')],
    'Wednesday': [('11:30','12:00'), ('12:30','13:00'), ('15:30','16:30')],
    'Thursday': [('10:30','11:00'), ('12:00','13:30'), ('15:00','15:30'), ('16:00','16:30')]
}

philip_busy = {
    'Monday': [('9:00','17:00')],
    'Tuesday': [('9:00','11:00'), ('11:30','12:00'), ('13:00','13:30'), ('14:00','14:30'), ('15:00','16:30')],
    'Wednesday': [('9:00','10:00'), ('11:00','12:00'), ('12:30','16:00'), ('16:30','17:00')],
    'Thursday': [('9:00','10:30'), ('11:00','12:30'), ('13:00','17:00')]
}

# Since Philip cannot meet on Wednesday, and Monday is fully busy for Philip, we consider only Tuesday and Thursday.
candidate_days = ['Tuesday', 'Thursday']
meeting_duration = 60  # minutes
work_end = 480  # 17:00 in minutes from 9:00 (which is 0)

found = False
result_day = ""
result_time_str = ""

for day in candidate_days:
    busy_intervals = []
    
    # Add Laura's busy intervals for this day
    for interval in laura_busy[day]:
        start_min = time_to_minutes(interval[0])
        end_min = time_to_minutes(interval[1])
        busy_intervals.append([start_min, end_min])
    
    # Add Philip's busy intervals for this day
    for interval in philip_busy[day]:
        start_min = time_to_minutes(interval[0])
        end_min = time_to_minutes(interval[1])
        busy_intervals.append([start_min, end_min])
    
    # If no busy intervals, the whole day is free
    if not busy_intervals:
        if work_end >= meeting_duration:
            meeting_start = 0
            start_str = minutes_to_time(meeting_start)
            end_str = minutes_to_time(meeting_start + meeting_duration)
            result_day = day
            result_time_str = f"{start_str}:{end_str}"
            found = True
            break
        else:
            continue
    
    # Merge busy intervals
    busy_intervals.sort(key=lambda x: x[0])
    merged = []
    start_current, end_current = busy_intervals[0]
    for i in range(1, len(busy_intervals)):
        s, e = busy_intervals[i]
        if s <= end_current:
            end_current = max(end_current, e)
        else:
            merged.append([start_current, end_current])
            start_current, end_current = s, e
    merged.append([start_current, end_current])
    
    # Find free intervals
    free_intervals = []
    current_start = 0
    for interval in merged:
        s, e = interval
        if current_start < s:
            free_intervals.append([current_start, s])
        current_start = e
    if current_start < work_end:
        free_intervals.append([current_start, work_end])
    
    # Check for a free interval of at least meeting_duration
    for interval in free_intervals:
        start_free, end_free = interval
        duration = end_free - start_free
        if duration >= meeting_duration:
            meeting_start = start_free
            start_str = minutes_to_time(meeting_start)
            end_str = minutes_to_time(meeting_start + meeting_duration)
            result_day = day
            result_time_str = f"{start_str}:{end_str}"
            found = True
            break
    if found:
        break

# Output the result
if found:
    print(result_day)
    print(result_time_str)
else:
    # According to the problem, there exists a solution, so this should not happen.
    print("No suitable time found")