def time_to_min(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

laura_busy = {
    'Monday': [('10:30', '11:00'), ('12:30', '13:00'), ('14:30', '15:30'), ('16:00', '17:00')],
    'Tuesday': [('9:30', '10:00'), ('11:00', '11:30'), ('13:00', '13:30'), ('14:30', '15:00'), ('16:00', '17:00')],
    'Wednesday': [('11:30', '12:00'), ('12:30', '13:00'), ('15:30', '16:30')],
    'Thursday': [('10:30', '11:00'), ('12:00', '13:30'), ('15:00', '15:30'), ('16:00', '16:30')]
}

philip_busy = {
    'Monday': [('9:00', '17:00')],
    'Tuesday': [('9:00', '11:00'), ('11:30', '12:00'), ('13:00', '13:30'), ('14:00', '14:30'), ('15:00', '16:30')],
    'Wednesday': [('9:00', '10:00'), ('11:00', '12:00'), ('12:30', '16:00'), ('16:30', '17:00')],
    'Thursday': [('9:00', '10:30'), ('11:00', '12:30'), ('13:00', '17:00')]
}

days = ['Monday', 'Tuesday', 'Thursday']
work_start = 540  # 9:00 in minutes
work_end = 1020    # 17:00 in minutes

found = False
for day in days:
    intervals = []
    for interval in laura_busy[day]:
        start_min = time_to_min(interval[0])
        end_min = time_to_min(interval[1])
        intervals.append((start_min, end_min))
    
    for interval in philip_busy[day]:
        start_min = time_to_min(interval[0])
        end_min = time_to_min(interval[1])
        intervals.append((start_min, end_min))
    
    if not intervals:
        free_start = work_start
        free_end = work_end
        duration = free_end - free_start
        if duration >= 60:
            meeting_start = free_start
            meeting_end = meeting_start + 60
            start_str = min_to_time(meeting_start)
            end_str = min_to_time(meeting_end)
            print(day)
            print(f"{start_str}:{end_str}")
            found = True
            break
    else:
        intervals.sort(key=lambda x: x[0])
        merged = []
        current_start, current_end = intervals[0]
        for i in range(1, len(intervals)):
            s, e = intervals[i]
            if s <= current_end:
                if e > current_end:
                    current_end = e
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
        
        free_intervals = []
        current = work_start
        for start, end in merged:
            if current < start:
                free_intervals.append((current, start))
                current = end
            else:
                if end > current:
                    current = end
        if current < work_end:
            free_intervals.append((current, work_end))
            
        for free_start, free_end in free_intervals:
            duration = free_end - free_start
            if duration >= 60:
                meeting_start = free_start
                meeting_end = meeting_start + 60
                start_str = min_to_time(meeting_start)
                end_str = min_to_time(meeting_end)
                print(day)
                print(f"{start_str}:{end_str}")
                found = True
                break
    if found:
        break

if not found:
    print("No suitable time found")