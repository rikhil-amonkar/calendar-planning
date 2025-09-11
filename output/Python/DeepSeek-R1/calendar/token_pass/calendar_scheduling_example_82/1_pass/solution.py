def main():
    # Convert time string to minutes since 00:00
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        return int(parts[0]) * 60 + int(parts[1])
    
    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"
    
    # Work hours
    work_start = time_to_minutes('9:00')
    work_end = time_to_minutes('17:00')
    meeting_duration = 30
    
    # Busy intervals for each participant in minutes
    busy_intervals = [
        (time_to_minutes('9:30'), time_to_minutes('10:30')),
        (time_to_minutes('15:00'), time_to_minutes('15:30')),
        (time_to_minutes('16:00'), time_to_minutes('16:30')),
        (time_to_minutes('9:00'), time_to_minutes('12:00')),
        (time_to_minutes('13:00'), time_to_minutes('15:00')),
        (time_to_minutes('15:30'), time_to_minutes('16:00')),
        (time_to_minutes('16:30'), time_to_minutes('17:00'))
    ]
    
    # Merge busy intervals
    busy_intervals.sort(key=lambda x: x[0])
    merged = []
    current_start, current_end = busy_intervals[0]
    for start, end in busy_intervals[1:]:
        if start <= current_end:
            current_end = max(current_end, end)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = start, end
    merged.append((current_start, current_end))
    
    # Find free intervals within work hours
    free_intervals = []
    previous_end = work_start
    for start, end in merged:
        if start > previous_end:
            free_intervals.append((previous_end, start))
        previous_end = max(previous_end, end)
    if previous_end < work_end:
        free_intervals.append((previous_end, work_end))
    
    # Find first free interval that can accommodate the meeting
    for start, end in free_intervals:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = meeting_start + meeting_duration
            time_range = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
            print(f"Monday {time_range}")
            return
    
    print("No suitable time found")

if __name__ == "__main__":
    main()