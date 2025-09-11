def main():
    # Define work hours: 9:00 to 17:00, represented in minutes from 9:00 (0 to 480)
    work_start = 0
    work_end = 480
    meeting_duration = 30
    
    # Harold's busy intervals on Tuesday in minutes from 9:00
    busy_tuesday = [
        (0, 30),    # 9:00-9:30
        (90, 150),  # 10:30-11:30
        (210, 270), # 12:30-13:30
        (330, 390), # 14:30-15:30
        (420, 480)  # 16:00-17:00
    ]
    
    # Find free intervals on Tuesday
    free_intervals = []
    current_time = work_start
    for start, end in sorted(busy_tuesday, key=lambda x: x[0]):
        if current_time < start:
            free_intervals.append((current_time, start))
        current_time = end
    if current_time < work_end:
        free_intervals.append((current_time, work_end))
    
    # Preference: avoid Tuesday before 14:30 (330 minutes from 9:00)
    preferred_start_min = 330
    
    # Find a free interval that meets duration and preference
    for start, end in free_intervals:
        duration = end - start
        if duration >= meeting_duration and start >= preferred_start_min:
            # Convert minutes to time strings
            start_min_from_9 = start
            end_min_from_9 = start + meeting_duration  # since we take the first available slot of sufficient duration
            # But we need to ensure we don't exceed the free interval, but since duration >= meeting_duration, it's fine
            # Actually, we can schedule from start to start+meeting_duration within the free interval
            start_time_min = start_min_from_9
            end_time_min = start_time_min + meeting_duration
            # Calculate hours and minutes from 9:00 base
            start_hour = 9 + start_time_min // 60
            start_minute = start_time_min % 60
            end_hour = 9 + end_time_min // 60
            end_minute = end_time_min % 60
            # Format to HH:MM
            time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
            print("Tuesday")
            print(time_str)
            return
    
    # If no preferred slot found, but according to task, there is a solution, so this should not happen
    print("No suitable time found")

if __name__ == "__main__":
    main()