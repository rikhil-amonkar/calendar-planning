def main():
    # Define work hours in minutes (9:00 to 17:00)
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes

    # Samuel's busy times in minutes for each day
    samuel_busy = {
        'Monday': [
            (10*60+30, 11*60),      # 10:30-11:00
            (12*60, 12*60+30),      # 12:00-12:30
            (13*60, 15*60),         # 13:00-15:00
            (15*60+30, 16*60+30)   # 15:30-16:30
        ],
        'Tuesday': [
            (9*60, 12*60),         # 9:00-12:00
            (14*60, 15*60+30),     # 14:00-15:30
            (16*60+30, 17*60)      # 16:30-17:00
        ],
        'Wednesday': [
            (10*60+30, 11*60),     # 10:30-11:00
            (11*60+30, 12*60),     # 11:30-12:00
            (12*60+30, 13*60),     # 12:30-13:00
            (14*60, 14*60+30),     # 14:00-14:30
            (15*60, 16*60)         # 15:00-16:00
        ]
    }

    # Days to check in order (Monday, Tuesday, Wednesday)
    days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_duration = 30  # minutes

    for day in days:
        # Get busy intervals for the day, sorted by start time
        busy_today = samuel_busy.get(day, [])
        busy_today.sort(key=lambda x: x[0])
        
        # Compute free intervals during work hours
        free_intervals = []
        current = work_start
        
        for start, end in busy_today:
            if current < start:
                # Free interval from current to start of next busy
                free_intervals.append((current, start))
            current = max(current, end)
        
        # Check after last busy interval until work_end
        if current < work_end:
            free_intervals.append((current, work_end))
        
        # Check each free interval for a slot of at least meeting_duration
        for start_minutes, end_minutes in free_intervals:
            if end_minutes - start_minutes >= meeting_duration:
                # Found a slot: take the earliest possible (start of interval)
                meeting_end_minutes = start_minutes + meeting_duration
                
                # Format start and end times as HH:MM
                start_hour = start_minutes // 60
                start_minute = start_minutes % 60
                end_hour = meeting_end_minutes // 60
                end_minute = meeting_end_minutes % 60
                
                # Format time string as HH:MM:HH:MM
                time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
                
                # Output day and time string
                print(day)
                print(time_str)
                return
    
    # If no slot found (though problem states there is a solution)
    print("No suitable time found")

if __name__ == "__main__":
    main()