def time_to_min(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for i in range(1, len(intervals)):
        current = intervals[i]
        last = merged[-1]
        if current[0] <= last[1]:
            last_end = max(last[1], current[1])
            merged[-1] = (last[0], last_end)
        else:
            merged.append(current)
    return merged

def main():
    work_start = 9 * 60  # 540 minutes (9:00)
    work_end = 17 * 60   # 1020 minutes (17:00)
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    
    # Nicole's busy times per day
    nicole_busy = {
        'Tuesday': [('16:00', '16:30')],
        'Wednesday': [('15:00', '15:30')],
        'Friday': [('12:00', '12:30'), ('15:30', '16:00')]
    }
    
    # Daniel's busy times per day
    daniel_busy = {
        'Monday': [('9:00', '12:30'), ('13:00', '13:30'), ('14:00', '16:30')],
        'Tuesday': [('9:00', '10:30'), ('11:30', '12:30'), ('13:00', '13:30'), ('15:00', '16:00'), ('16:30', '17:00')],
        'Wednesday': [('9:00', '10:00'), ('11:00', '12:30'), ('13:00', '13:30'), ('14:00', '14:30'), ('16:30', '17:00')],
        'Thursday': [('11:00', '12:00'), ('13:00', '14:00'), ('15:00', '15:30')],
        'Friday': [('10:00', '11:00'), ('11:30', '12:00'), ('12:30', '14:30'), ('15:00', '15:30'), ('16:00', '16:30')]
    }
    
    for day in days:
        all_busy = []
        # Collect Nicole's busy intervals for the day
        if day in nicole_busy:
            for interval in nicole_busy[day]:
                start_min = time_to_min(interval[0])
                end_min = time_to_min(interval[1])
                all_busy.append((start_min, end_min))
        
        # Collect Daniel's busy intervals for the day
        if day in daniel_busy:
            for interval in daniel_busy[day]:
                start_min = time_to_min(interval[0])
                end_min = time_to_min(interval[1])
                all_busy.append((start_min, end_min))
        
        # If no busy intervals, entire workday is free
        if not all_busy:
            meeting_start = work_start
            meeting_end = meeting_start + 60
            start_str = min_to_time(meeting_start)
            end_str = min_to_time(meeting_end)
            print(day)
            print(f"{start_str}:{end_str}")
            return
        
        # Merge busy intervals
        merged_busy = merge_intervals(all_busy)
        
        # Calculate free intervals
        free_intervals = []
        current = work_start
        for start, end in merged_busy:
            if current < start:
                free_intervals.append((current, start))
            current = max(current, end)
        if current < work_end:
            free_intervals.append((current, work_end))
        
        # Check each free interval for a 60-minute slot
        for start, end in free_intervals:
            if end - start >= 60:
                meeting_start = start
                meeting_end = meeting_start + 60
                start_str = min_to_time(meeting_start)
                end_str = min_to_time(meeting_end)
                print(day)
                print(f"{start_str}:{end_str}")
                return

if __name__ == "__main__":
    main()