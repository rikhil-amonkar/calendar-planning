def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def main():
    # Define the busy schedules for Robert and Ralph
    robert_busy = {
        'Monday': [('11:00', '11:30'), ('14:00', '14:30'), ('15:30', '16:00')],
        'Tuesday': [('10:30', '11:00'), ('15:00', '15:30')],
        'Wednesday': [('10:00', '11:00'), ('11:30', '12:00'), ('12:30', '13:00'), ('13:30', '14:00'), ('15:00', '15:30'), ('16:00', '16:30')]
    }
    ralph_busy = {
        'Monday': [('10:00', '13:30'), ('14:00', '14:30'), ('15:00', '17:00')],
        'Tuesday': [('9:00', '9:30'), ('10:00', '10:30'), ('11:00', '11:30'), ('12:00', '13:00'), ('14:00', '15:30'), ('16:00', '17:00')],
        'Wednesday': [('10:30', '11:00'), ('11:30', '12:00'), ('13:00', '14:30'), ('16:30', '17:00')]
    }
    
    # Work hours (9:00 to 17:00) in minutes
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes
    meeting_duration = 30  # minutes
    
    # Days to check in order: Tuesday, Wednesday, Monday (to avoid Monday if possible)
    days_to_check = ['Tuesday', 'Wednesday', 'Monday']
    
    for day in days_to_check:
        # Collect all busy intervals for this day from both participants
        all_busy = []
        if day in robert_busy:
            for interval in robert_busy[day]:
                start_min = time_to_minutes(interval[0])
                end_min = time_to_minutes(interval[1])
                all_busy.append((start_min, end_min))
        if day in ralph_busy:
            for interval in ralph_busy[day]:
                start_min = time_to_minutes(interval[0])
                end_min = time_to_minutes(interval[1])
                all_busy.append((start_min, end_min))
        
        # If no busy intervals, the whole day is free
        if not all_busy:
            meeting_start = work_start
            meeting_end = meeting_start + meeting_duration
            start_str = minutes_to_time(meeting_start)
            end_str = minutes_to_time(meeting_end)
            time_range_str = f"{start_str.replace(':', '')[:2]}:{start_str[-2:]}:{end_str.replace(':', '')[:2]}:{end_str[-2:]}"
            print(day)
            print(time_range_str)
            return
        
        # Sort intervals by start time
        all_busy.sort(key=lambda x: x[0])
        
        # Merge overlapping or adjacent intervals
        merged = []
        current_start, current_end = all_busy[0]
        for i in range(1, len(all_busy)):
            s, e = all_busy[i]
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))
        
        # Find free intervals within work hours
        free_intervals = []
        # Before first busy interval
        if work_start < merged[0][0]:
            free_intervals.append((work_start, merged[0][0]))
        # Between busy intervals
        for i in range(len(merged) - 1):
            current_end = merged[i][1]
            next_start = merged[i+1][0]
            if current_end < next_start:
                free_intervals.append((current_end, next_start))
        # After last busy interval
        if merged[-1][1] < work_end:
            free_intervals.append((merged[-1][1], work_end))
        
        # Check each free interval for a slot of at least meeting_duration
        for free_start, free_end in free_intervals:
            if free_end - free_start >= meeting_duration:
                meeting_start = free_start
                meeting_end = free_start + meeting_duration
                start_str = minutes_to_time(meeting_start)
                end_str = minutes_to_time(meeting_end)
                # Format as HH:MM:HH:MM
                time_range_str = f"{start_str.replace(':', '')[:2]}:{start_str[-2:]}:{end_str.replace(':', '')[:2]}:{end_str[-2:]}"
                print(day)
                print(time_range_str)
                return

if __name__ == "__main__":
    main()