def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def main():
    # Define work hours (9:00 to 17:00) in minutes
    work_start = 9 * 60  # 540 minutes (9:00)
    work_end = 17 * 60   # 1020 minutes (17:00)
    meeting_duration = 60  # 60 minutes

    # Define busy times for Carl and Margaret for each day
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
    
    # Days in order of preference (avoid Thursday if possible)
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    
    for day in days:
        busy_intervals = []
        
        # Add Carl's busy intervals for the day
        if day in carl_busy:
            for interval in carl_busy[day]:
                start_min = time_to_minutes(interval[0])
                end_min = time_to_minutes(interval[1])
                busy_intervals.append([start_min, end_min])
        
        # Add Margaret's busy intervals for the day
        if day in margaret_busy:
            for interval in margaret_busy[day]:
                start_min = time_to_minutes(interval[0])
                end_min = time_to_minutes(interval[1])
                busy_intervals.append([start_min, end_min])
        
        # If no busy intervals, the entire workday is free
        if not busy_intervals:
            # Entire workday free: check if long enough
            if work_end - work_start >= meeting_duration:
                start_time = work_start
                end_time = start_time + meeting_duration
                start_str = minutes_to_time(start_time)
                end_str = minutes_to_time(end_time)
                print(day)
                print(f"{start_str}:{end_str}")
                return
        
        # Sort and merge busy intervals
        busy_intervals.sort(key=lambda x: x[0])
        merged_busy = []
        current_start, current_end = busy_intervals[0]
        for i in range(1, len(busy_intervals)):
            if busy_intervals[i][0] <= current_end:
                current_end = max(current_end, busy_intervals[i][1])
            else:
                merged_busy.append([current_start, current_end])
                current_start, current_end = busy_intervals[i]
        merged_busy.append([current_start, current_end])
        
        # Find free intervals within work hours
        free_intervals = []
        current = work_start
        for interval in merged_busy:
            if current < interval[0]:
                free_intervals.append([current, interval[0]])
                current = interval[1]
            else:
                current = max(current, interval[1])
        if current < work_end:
            free_intervals.append([current, work_end])
        
        # Check each free interval for sufficient length
        for interval in free_intervals:
            start_free, end_free = interval
            if end_free - start_free >= meeting_duration:
                meeting_start = start_free
                meeting_end = meeting_start + meeting_duration
                start_str = minutes_to_time(meeting_start)
                end_str = minutes_to_time(meeting_end)
                print(day)
                print(f"{start_str}:{end_str}")
                return
    
    # If no slot found (though problem states there is a solution)
    print("No suitable slot found")

if __name__ == "__main__":
    main()