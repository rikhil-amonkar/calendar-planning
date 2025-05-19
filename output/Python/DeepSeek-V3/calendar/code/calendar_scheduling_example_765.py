def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_duration = 30  # minutes

    # Define busy times for each person in minutes since midnight
    joshua_busy = {
        'Monday': [(15 * 60, 15 * 60 + 30)],
        'Tuesday': [(11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60)],
        'Wednesday': []
    }
    
    joyce_busy = {
        'Monday': [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60), (11 * 60 + 30, 12 * 60 + 30),
                   (13 * 60, 15 * 60), (15 * 60 + 30, 17 * 60)],
        'Tuesday': [(9 * 60, 17 * 60)],
        'Wednesday': [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60), (12 * 60 + 30, 15 * 60 + 30),
                      (16 * 60, 16 * 60 + 30)]
    }
    
    # Joyce's preference: not before 12:00 on Monday
    joyce_preference = {
        'Monday': 12 * 60,
        'Tuesday': 0,
        'Wednesday': 0
    }
    
    # Iterate through each day to find a suitable time
    for day in days:
        # Collect all busy intervals for both participants
        busy_intervals = joshua_busy[day] + joyce_busy[day]
        busy_intervals.sort()  # Sort by start time
        
        # Find the earliest possible start time considering Joyce's preference
        current_start = max(work_start, joyce_preference[day])
        
        # Check the time slots between busy intervals
        for interval in busy_intervals:
            interval_start, interval_end = interval
            if current_start + meeting_duration <= interval_start:
                # Found a suitable slot
                start_time = current_start
                end_time = start_time + meeting_duration
                # Format the time as HH:MM:HH:MM
                start_str = f"{start_time // 60:02d}:{start_time % 60:02d}"
                end_str = f"{end_time // 60:02d}:{end_time % 60:02d}"
                print(f"{day}:{start_str}:{end_str}")
                return
            # Update current_start to the end of the current busy interval
            if interval_end > current_start:
                current_start = interval_end
        
        # Check the time after the last busy interval
        if current_start + meeting_duration <= work_end:
            start_time = current_start
            end_time = start_time + meeting_duration
            start_str = f"{start_time // 60:02d}:{start_time % 60:02d}"
            end_str = f"{end_time // 60:02d}:{end_time % 60:02d}"
            print(f"{day}:{start_str}:{end_str}")
            return
    
    print("No suitable time found.")

find_meeting_time()