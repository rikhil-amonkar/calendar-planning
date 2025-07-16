def time_str_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour:02d}:{minute:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    start, end = sorted_intervals[0]
    for s, e in sorted_intervals[1:]:
        if s <= end:
            end = max(end, e)
        else:
            merged.append((start, end))
            start, end = s, e
    merged.append((start, end))
    return merged

def find_free_intervals(busy_intervals, work_start, work_end):
    if not busy_intervals:
        return [(work_start, work_end)]
    merged_busy = merge_intervals(busy_intervals)
    free_intervals = []
    current = work_start
    for start, end in merged_busy:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def main():
    work_start_min = 9 * 60  # 9:00
    work_end_min = 17 * 60   # 17:00
    duration = 30

    # Define the schedules
    terry_schedule = {
        'Monday': [('10:30', '11:00'), ('12:30', '14:00'), ('15:00', '17:00')],
        'Tuesday': [('9:30', '10:00'), ('10:30', '11:00'), ('14:00', '14:30'), ('16:00', '16:30')],
        'Wednesday': [('9:30', '10:30'), ('11:00', '12:00'), ('13:00', '13:30'), ('15:00', '16:00'), ('16:30', '17:00')],
        'Thursday': [('9:30', '10:00'), ('12:00', '12:30'), ('13:00', '14:30'), ('16:00', '16:30')],
        'Friday': [('9:00', '11:30'), ('12:00', '12:30'), ('13:30', '16:00'), ('16:30', '17:00')]
    }

    frances_schedule = {
        'Monday': [('9:30', '11:00'), ('11:30', '13:00'), ('14:00', '14:30'), ('15:00', '16:00')],
        'Tuesday': [('9:00', '9:30'), ('10:00', '10:30'), ('11:00', '12:00'), ('13:00', '14:30'), ('15:30', '16:30')],
        'Wednesday': [('9:30', '10:00'), ('10:30', '11:00'), ('11:30', '16:00'), ('16:30', '17:00')],
        'Thursday': [('11:00', '12:30'), ('14:30', '17:00')],
        'Friday': [('9:30', '10:30'), ('11:00', '12:30'), ('13:00', '16:00'), ('16:30', '17:00')]
    }

    # Order of days: avoid Tuesday if possible
    days = ['Monday', 'Wednesday', 'Thursday', 'Friday', 'Tuesday']
    
    for day in days:
        busy_intervals = []
        # Collect Terry's busy intervals for the day
        if day in terry_schedule:
            for interval in terry_schedule[day]:
                start_min = time_str_to_minutes(interval[0])
                end_min = time_str_to_minutes(interval[1])
                busy_intervals.append((start_min, end_min))
        # Collect Frances' busy intervals for the day
        if day in frances_schedule:
            for interval in frances_schedule[day]:
                start_min = time_str_to_minutes(interval[0])
                end_min = time_str_to_minutes(interval[1])
                busy_intervals.append((start_min, end_min))
        
        # Find free intervals for the day
        free_intervals = find_free_intervals(busy_intervals, work_start_min, work_end_min)
        
        # Check each free interval for a slot of duration
        for start, end in free_intervals:
            if end - start >= duration:
                meeting_start = start
                meeting_end = start + duration
                start_str = minutes_to_time_str(meeting_start)
                end_str = minutes_to_time_str(meeting_end)
                time_range_str = f"{start_str}:{end_str}"
                print(day)
                print(time_range_str)
                return
    
    # Should not reach here because solution exists
    print("No suitable time found")

if __name__ == "__main__":
    main()