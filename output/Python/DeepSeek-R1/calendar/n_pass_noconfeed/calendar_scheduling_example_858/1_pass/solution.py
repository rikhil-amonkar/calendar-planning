def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time_str(total_minutes):
    hours = total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def main():
    carl_busy = {
        'Monday': [('11:00', '11:30')],
        'Tuesday': [('14:30', '15:00')],
        'Wednesday': [('10:00', '11:30'), ('13:00', '13:30')],
        'Thursday': [('13:30', '14:00'), ('16:00', '16:30')]
    }
    
    margaret_busy = {
        'Monday': [('9:00', '10:30'), ('11:00', '17:00')],
        'Tuesday': [('9:30', '12:00'), ('13:30', '14:00'), ('15:30', '17:00')],
        'Wednesday': [('9:30', '12:00'), ('12:30', '13:00'), ('13:30', '14:30'), ('15:00', '17:00')],
        'Thursday': [('10:00', '12:00'), ('12:30', '14:00'), ('14:30', '17:00')]
    }
    
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    work_start = time_str_to_minutes('9:00')
    work_end = time_str_to_minutes('17:00')
    meeting_duration = 60
    
    for day in days:
        if day == 'Thursday':
            continue  # Skip Thursday initially
        
        intervals = []
        
        if day in carl_busy:
            for interval in carl_busy[day]:
                start_min = time_str_to_minutes(interval[0])
                end_min = time_str_to_minutes(interval[1])
                intervals.append([start_min, end_min])
        
        if day in margaret_busy:
            for interval in margaret_busy[day]:
                start_min = time_str_to_minutes(interval[0])
                end_min = time_str_to_minutes(interval[1])
                intervals.append([start_min, end_min])
        
        if not intervals:
            free_start = work_start
            free_end = work_end
            if free_end - free_start >= meeting_duration:
                meeting_start = free_start
                meeting_end = meeting_start + meeting_duration
                start_str = minutes_to_time_str(meeting_start)
                end_str = minutes_to_time_str(meeting_end)
                print(day)
                print(f"{start_str}:{end_str}")
                return
        
        intervals.sort(key=lambda x: x[0])
        merged = []
        for interval in intervals:
            if not merged:
                merged.append(interval)
            else:
                last = merged[-1]
                if interval[0] <= last[1]:
                    last[1] = max(last[1], interval[1])
                else:
                    merged.append(interval)
        
        free_intervals = []
        current = work_start
        for interval in merged:
            if current < interval[0]:
                free_intervals.append([current, interval[0]])
            current = max(current, interval[1])
        if current < work_end:
            free_intervals.append([current, work_end])
        
        for free in free_intervals:
            start_free, end_free = free
            duration = end_free - start_free
            if duration >= meeting_duration:
                meeting_start = start_free
                meeting_end = meeting_start + meeting_duration
                start_str = minutes_to_time_str(meeting_start)
                end_str = minutes_to_time_str(meeting_end)
                print(day)
                print(f"{start_str}:{end_str}")
                return
    
    # If no slot found in Monday-Wednesday, try Thursday
    day = 'Thursday'
    intervals = []
    if day in carl_busy:
        for interval in carl_busy[day]:
            start_min = time_str_to_minutes(interval[0])
            end_min = time_str_to_minutes(interval[1])
            intervals.append([start_min, end_min])
    
    if day in margaret_busy:
        for interval in margaret_busy[day]:
            start_min = time_str_to_minutes(interval[0])
            end_min = time_str_to_minutes(interval[1])
            intervals.append([start_min, end_min])
    
    if not intervals:
        free_start = work_start
        free_end = work_end
        if free_end - free_start >= meeting_duration:
            meeting_start = free_start
            meeting_end = meeting_start + meeting_duration
            start_str = minutes_to_time_str(meeting_start)
            end_str = minutes_to_time_str(meeting_end)
            print(day)
            print(f"{start_str}:{end_str}")
            return
    
    intervals.sort(key=lambda x: x[0])
    merged = []
    for interval in intervals:
        if not merged:
            merged.append(interval)
        else:
            last = merged[-1]
            if interval[0] <= last[1]:
                last[1] = max(last[1], interval[1])
            else:
                merged.append(interval)
    
    free_intervals = []
    current = work_start
    for interval in merged:
        if current < interval[0]:
            free_intervals.append([current, interval[0]])
        current = max(current, interval[1])
    if current < work_end:
        free_intervals.append([current, work_end])
    
    for free in free_intervals:
        start_free, end_free = free
        duration = end_free - start_free
        if duration >= meeting_duration:
            meeting_start = start_free
            meeting_end = meeting_start + meeting_duration
            start_str = minutes_to_time_str(meeting_start)
            end_str = minutes_to_time_str(meeting_end)
            print(day)
            print(f"{start_str}:{end_str}")
            return

if __name__ == '__main__':
    main()