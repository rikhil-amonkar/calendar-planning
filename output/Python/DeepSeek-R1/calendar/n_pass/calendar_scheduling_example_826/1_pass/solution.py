def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return hour, minute

James_busy = {
    'Monday': [('9:00','9:30'), ('10:30','11:00'), ('12:30','13:00'), ('14:30','15:30'), ('16:30','17:00')],
    'Tuesday': [('9:00','11:00'), ('11:30','12:00'), ('12:30','15:30'), ('16:00','17:00')],
    'Wednesday': [('10:00','11:00'), ('12:00','13:00'), ('13:30','16:00')],
    'Thursday': [('9:30','11:30'), ('12:00','12:30'), ('13:00','13:30'), ('14:00','14:30'), ('16:30','17:00')]
}

days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
duration = 30  # minutes

for day in days:
    busy_intervals = James_busy[day]
    busy_minutes = []
    for interval in busy_intervals:
        start_min = time_to_minutes(interval[0])
        end_min = time_to_minutes(interval[1])
        busy_minutes.append((start_min, end_min))
    
    busy_minutes.sort(key=lambda x: x[0])
    
    work_start = time_to_minutes('9:00')
    work_end = time_to_minutes('17:00')
    free_intervals = []
    current = work_start
    
    for start, end in busy_minutes:
        if current < start:
            free_intervals.append((current, start))
        if current < end:
            current = end
    
    if current < work_end:
        free_intervals.append((current, work_end))
    
    for start, end in free_intervals:
        if end - start >= duration:
            meeting_start = start
            meeting_end = meeting_start + duration
            start_hour, start_minute = minutes_to_time(meeting_start)
            end_hour, end_minute = minutes_to_time(meeting_end)
            time_str = f"{start_hour}:{start_minute:02d}:{end_hour}:{end_minute:02d}"
            print(day)
            print(time_str)
            exit(0)

# If no solution found, but problem states one exists
print("No solution found, but there should be one.")