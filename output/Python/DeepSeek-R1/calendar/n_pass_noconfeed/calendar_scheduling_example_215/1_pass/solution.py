def main():
    # Meeting duration in minutes
    duration = 30
    # Work hours: 9:00 to 17:00 (8 hours = 480 minutes), using 9:00 as 0 minutes
    work_start = 0
    work_end = 480  # 17:00 - 9:00 = 8 hours = 480 minutes
    day = "Monday"

    # Helper function to convert time string to minutes from 9:00
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1])
        return (hour - 9) * 60 + minute

    # Collect all busy intervals
    busy_intervals = []
    
    # Cynthia's busy times
    cynthia_busy = ["9:30 to 10:30", "11:30 to 12:00", "13:00 to 13:30", "15:00 to 16:00"]
    for interval in cynthia_busy:
        start_str, end_str = interval.split(' to ')
        start_min = time_to_minutes(start_str)
        end_min = time_to_minutes(end_str)
        busy_intervals.append((start_min, end_min))
    
    # Lauren's busy times
    lauren_busy = ["9:00 to 9:30", "10:30 to 11:00", "11:30 to 12:00", "13:00 to 13:30", "14:00 to 14:30", "15:00 to 15:30", "16:00 to 17:00"]
    for interval in lauren_busy:
        start_str, end_str = interval.split(' to ')
        start_min = time_to_minutes(start_str)
        end_min = time_to_minutes(end_str)
        busy_intervals.append((start_min, end_min))
    
    # Robert's busy times
    robert_busy = ["10:30 to 11:00", "11:30 to 12:00", "12:30 to 13:30", "14:00 to 16:00"]
    for interval in robert_busy:
        start_str, end_str = interval.split(' to ')
        start_min = time_to_minutes(start_str)
        end_min = time_to_minutes(end_str)
        busy_intervals.append((start_min, end_min))
    
    # Steven and Roy are free all day, so no intervals added for them

    # Merge busy intervals
    if not busy_intervals:
        merged_busy = []
    else:
        busy_intervals.sort(key=lambda x: x[0])
        merged_busy = []
        current_start, current_end = busy_intervals[0]
        for interval in busy_intervals[1:]:
            if interval[0] <= current_end:
                current_end = max(current_end, interval[1])
            else:
                merged_busy.append((current_start, current_end))
                current_start, current_end = interval
        merged_busy.append((current_start, current_end))
    
    # Find free intervals
    free_intervals = []
    current_time = work_start
    for start, end in merged_busy:
        if current_time < start:
            free_intervals.append((current_time, start))
        current_time = max(current_time, end)
    if current_time < work_end:
        free_intervals.append((current_time, work_end))
    
    # Find the earliest free interval that can fit the meeting
    meeting_start = None
    for start, end in free_intervals:
        if end - start >= duration:
            meeting_start = start
            break
    
    if meeting_start is None:
        # According to the problem, there is a solution, so this should not happen
        print("No suitable time found")
        return

    meeting_end = meeting_start + duration
    
    # Convert meeting times to HH:MM format
    def minutes_to_time(minutes):
        total_minutes = minutes
        hour = 9 + total_minutes // 60
        minute = total_minutes % 60
        return f"{hour:02d}:{minute:02d}"
    
    start_time_str = minutes_to_time(meeting_start)
    end_time_str = minutes_to_time(meeting_end)
    
    # Format the time range as HH:MM:HH:MM
    time_range_str = f"{start_time_str}:{end_time_str}"
    
    # Output the day and time range
    print(day)
    print(time_range_str)

if __name__ == "__main__":
    main()