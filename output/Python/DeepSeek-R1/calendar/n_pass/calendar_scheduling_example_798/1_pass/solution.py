def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1]) if len(parts) > 1 else 0
    return (hours - 9) * 60 + minutes

def minutes_to_time(minutes_val):
    total_minutes = minutes_val
    hours = 9 + total_minutes // 60
    minutes = total_minutes % 60
    return f"{hours}:{minutes:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    start, end = sorted_intervals[0]
    for interval in sorted_intervals[1:]:
        if interval[0] <= end:
            if interval[1] > end:
                end = interval[1]
        else:
            merged.append([start, end])
            start, end = interval
    merged.append([start, end])
    return merged

def find_free_intervals(busy_intervals, day_end=480):
    free_intervals = []
    if not busy_intervals:
        return [(0, day_end)]
    current = 0
    for start, end in busy_intervals:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < day_end:
        free_intervals.append((current, day_end))
    return free_intervals

def main():
    nancy_schedule = {
        'Monday': ['10:00-10:30', '11:30-12:30', '13:30-14:00', '14:30-15:30', '16:00-17:00'],
        'Tuesday': ['9:30-10:30', '11:00-11:30', '12:00-12:30', '13:00-13:30', '15:30-16:00'],
        'Wednesday': ['10:00-11:30', '13:30-16:00']
    }
    
    jose_schedule = {
        'Monday': ['9:00-17:00'],
        'Tuesday': ['9:00-17:00'],
        'Wednesday': ['9:00-9:30', '10:00-12:30', '13:30-14:30', '15:00-17:00']
    }
    
    days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_duration = 30
    day_end_minutes = 480  # 17:00 is 480 minutes from 9:00
    
    for day in days:
        nancy_busy = []
        if day in nancy_schedule:
            for interval in nancy_schedule[day]:
                start_str, end_str = interval.split('-')
                start_min = time_to_minutes(start_str)
                end_min = time_to_minutes(end_str)
                nancy_busy.append([start_min, end_min])
        
        jose_busy = []
        if day in jose_schedule:
            for interval in jose_schedule[day]:
                start_str, end_str = interval.split('-')
                start_min = time_to_minutes(start_str)
                end_min = time_to_minutes(end_str)
                jose_busy.append([start_min, end_min])
        
        all_busy = nancy_busy + jose_busy
        merged_busy = merge_intervals(all_busy)
        free_intervals = find_free_intervals(merged_busy, day_end_minutes)
        
        for start_free, end_free in free_intervals:
            if end_free - start_free >= meeting_duration:
                meeting_start = start_free
                meeting_end = meeting_start + meeting_duration
                start_time_str = minutes_to_time(meeting_start)
                end_time_str = minutes_to_time(meeting_end)
                print(f"{day} {start_time_str}:{end_time_str}")
                return
    
    # According to the problem, a solution exists, so this line should not be reached.
    print("No meeting time found")

if __name__ == "__main__":
    main()