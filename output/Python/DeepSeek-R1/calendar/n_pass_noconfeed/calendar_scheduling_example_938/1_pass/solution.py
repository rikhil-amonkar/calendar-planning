def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    work_start = time_to_minutes('9:00')
    work_end = time_to_minutes('17:00')
    meeting_duration = 30
    
    # Define busy schedules
    Eugene_busy = {
        'Monday': [('11:00', '12:00'), ('13:30', '14:00'), ('14:30', '15:00'), ('16:00', '16:30')],
        'Wednesday': [('9:00', '9:30'), ('11:00', '11:30'), ('12:00', '12:30'), ('13:30', '15:00')],
        'Thursday': [('9:30', '10:00'), ('11:00', '12:30')],
        'Friday': [('10:30', '11:00'), ('12:00', '12:30'), ('13:00', '13:30')]
    }
    
    Eric_busy = {
        'Monday': [('9:00', '17:00')],
        'Tuesday': [('9:00', '17:00')],
        'Wednesday': [('9:00', '11:30'), ('12:00', '14:00'), ('14:30', '16:30')],
        'Thursday': [('9:00', '17:00')],
        'Friday': [('9:00', '11:00'), ('11:30', '17:00')]
    }
    
    # Days to check: Friday first (preferred), then Wednesday
    days_to_check = ['Friday', 'Wednesday']
    
    for day in days_to_check:
        busy_intervals = []
        
        # Add Eugene's busy intervals
        if day in Eugene_busy:
            for interval in Eugene_busy[day]:
                start_min = time_to_minutes(interval[0])
                end_min = time_to_minutes(interval[1])
                busy_intervals.append((start_min, end_min))
        
        # Add Eric's busy intervals
        if day in Eric_busy:
            for interval in Eric_busy[day]:
                start_min = time_to_minutes(interval[0])
                end_min = time_to_minutes(interval[1])
                busy_intervals.append((start_min, end_min))
        
        # If no busy intervals, the entire day is free
        if not busy_intervals:
            meeting_start = work_start
            meeting_end = meeting_start + meeting_duration
            start_str = minutes_to_time(meeting_start)
            end_str = minutes_to_time(meeting_end)
            print(day)
            print(f"{start_str}:{end_str}")
            return
        
        # Sort and merge busy intervals
        busy_intervals.sort(key=lambda x: x[0])
        merged = []
        current_start, current_end = busy_intervals[0]
        for s, e in busy_intervals[1:]:
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
        
        # Find free intervals
        free_intervals = []
        current = work_start
        for s, e in merged:
            if current < s:
                free_intervals.append((current, s))
            current = max(current, e)
        if current < work_end:
            free_intervals.append((current, work_end))
        
        # Check each free interval for a suitable slot
        for start_free, end_free in free_intervals:
            available_duration = end_free - start_free
            if available_duration >= meeting_duration:
                meeting_start = start_free
                meeting_end = meeting_start + meeting_duration
                start_str = minutes_to_time(meeting_start)
                end_str = minutes_to_time(meeting_end)
                print(day)
                print(f"{start_str}:{end_str}")
                return

if __name__ == "__main__":
    main()