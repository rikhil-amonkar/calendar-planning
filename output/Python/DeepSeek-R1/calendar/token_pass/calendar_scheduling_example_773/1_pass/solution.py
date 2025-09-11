def main():
    # Define work hours in minutes from 9:00 (0 minutes) to 17:00 (480 minutes)
    work_start = 0
    work_end = 480
    meeting_duration = 60  # minutes

    # Roy's busy intervals in minutes from 9:00 for each day
    busy_intervals = {
        'Monday': [[60, 150], [180, 240], [300, 330], [360, 480]],
        'Tuesday': [[90, 150], [180, 330], [360, 390], [420, 480]],
        'Wednesday': [[30, 150], [210, 300], [330, 390], [450, 480]]
    }

    days = ['Monday', 'Tuesday', 'Wednesday']

    for day in days:
        intervals = busy_intervals[day]
        free_intervals = []
        current = work_start
        
        # Generate free intervals by subtracting busy times from work hours
        for start, end in intervals:
            if current < start:
                free_intervals.append([current, start])
            current = end
        if current < work_end:
            free_intervals.append([current, work_end])
        
        # Check each free interval for sufficient duration
        for start_min, end_min in free_intervals:
            if end_min - start_min >= meeting_duration:
                # Convert start and end times to HH:MM format
                start_time_minutes = start_min
                end_time_minutes = start_min + meeting_duration
                
                start_hour = 9 + start_time_minutes // 60
                start_minute = start_time_minutes % 60
                end_hour = 9 + end_time_minutes // 60
                end_minute = end_time_minutes % 60
                
                # Format the output
                time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
                print(day)
                print(time_str)
                return
    
    print("No suitable time found.")

if __name__ == "__main__":
    main()