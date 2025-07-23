def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

work_start = 540  # 9:00 in minutes
work_end = 1020   # 17:00 in minutes

terry_busy = {
    'Monday': [('10:30','11:00'), ('12:30','14:00'), ('15:00','17:00')],
    'Tuesday': [('9:30','10:00'), ('10:30','11:00'), ('14:00','14:30'), ('16:00','16:30')],
    'Wednesday': [('9:30','10:30'), ('11:00','12:00'), ('13:00','13:30'), ('15:00','16:00'), ('16:30','17:00')],
    'Thursday': [('9:30','10:00'), ('12:00','12:30'), ('13:00','14:30'), ('16:00','16:30')],
    'Friday': [('9:00','11:30'), ('12:00','12:30'), ('13:30','16:00'), ('16:30','17:00')]
}

frances_busy = {
    'Monday': [('9:30','11:00'), ('11:30','13:00'), ('14:00','14:30'), ('15:00','16:00')],
    'Tuesday': [('9:00','9:30'), ('10:00','10:30'), ('11:00','12:00'), ('13:00','14:30'), ('15:30','16:30')],
    'Wednesday': [('9:30','10:00'), ('10:30','11:00'), ('11:30','16:00'), ('16:30','17:00')],
    'Thursday': [('11:00','12:30'), ('14:30','17:00')],
    'Friday': [('9:30','10:30'), ('11:00','12:30'), ('13:00','16:00'), ('16:30','17:00')]
}

# Convert the time strings to minutes
for day in terry_busy:
    terry_busy[day] = [(time_str_to_minutes(s), time_str_to_minutes(e)) for s, e in terry_busy[day]]

for day in frances_busy:
    frances_busy[day] = [(time_str_to_minutes(s), time_str_to_minutes(e)) for s, e in frances_busy[day]]

days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
found = False

for day in days:
    busy_intervals = []
    if day in terry_busy:
        busy_intervals.extend(terry_busy[day])
    if day in frances_busy:
        busy_intervals.extend(frances_busy[day])
        
    if not busy_intervals:
        free_interval_start = work_start
        free_interval_end = work_end
        duration = free_interval_end - free_interval_start
        if duration >= 30:
            meeting_start = free_interval_start
            meeting_end = meeting_start + 30
            start_h = meeting_start // 60
            start_m = meeting_start % 60
            end_h = meeting_end // 60
            end_m = meeting_end % 60
            time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
            print(time_str)
            print(day)
            found = True
            break
    else:
        busy_intervals.sort(key=lambda x: x[0])
        merged = []
        current_start, current_end = busy_intervals[0]
        for i in range(1, len(busy_intervals)):
            s, e = busy_intervals[i]
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
        
        free_intervals = []
        current = work_start
        for interval in merged:
            s, e = interval
            if current < s:
                free_intervals.append((current, s))
            current = e
        if current < work_end:
            free_intervals.append((current, work_end))
            
        for interval in free_intervals:
            start_free, end_free = interval
            duration = end_free - start_free
            if duration >= 30:
                meeting_start = start_free
                meeting_end = start_free + 30
                start_h = meeting_start // 60
                start_m = meeting_start % 60
                end_h = meeting_end // 60
                end_m = meeting_end % 60
                time_str = f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
                print(time_str)
                print(day)
                found = True
                break
        if found:
            break