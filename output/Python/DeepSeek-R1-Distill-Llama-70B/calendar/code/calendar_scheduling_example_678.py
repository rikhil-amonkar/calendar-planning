def find_meeting_time():
    # Define the schedules for each person as a dictionary with days and busy intervals
    russell_schedule = {
        'Monday': [(10.5*60, 11*60)],
        'Tuesday': [(13*60, 13.5*60)]
    }

    alexander_schedule = {
        'Monday': [(9*60, 11.5*60), (12*60, 14.5*60), (15*60, 17*60)],
        'Tuesday': [(9*60, 10*60), (13*60, 14*60), (15*60, 15.5*60), (16*60, 16.5*60)]
    }

    days = ['Monday', 'Tuesday']
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 60 minutes

    for day in days:
        # Get busy intervals for both participants on the current day
        russell_busy = russell_schedule.get(day, [])
        alexander_busy = alexander_schedule.get(day, [])

        # Combine and sort all busy intervals
        all_busy = []
        for interval in russell_busy:
            all_busy.append((interval[0], interval[1], 'Russell'))
        for interval in alexander_busy:
            all_busy.append((interval[0], interval[1], 'Alexander'))

        all_busy.sort()

        # Check for available slots
        current_time = start_time
        for busy_start, busy_end, person in all_busy:
            if current_time < busy_start:
                # Found an available slot
                if busy_start - current_time >= meeting_duration:
                    # Format the time
                    start_h = current_time // 60
                    start_m = current_time % 60
                    end_h = (current_time + meeting_duration) // 60
                    end_m = (current_time + meeting_duration) % 60
                    
                    # Convert to HH:MM format
                    start_time_str = f"{start_h:02d}:{start_m:02d}"
                    end_time_str = f"{end_h:02d}:{end_m:02d}"
                    
                    print(f"Meeting scheduled on {day} from {start_time_str} to {end_time_str}")
                    return
            current_time = max(current_time, busy_end)

        # Check if there's remaining time after last busy interval
        if current_time + meeting_duration <= end_time:
            start_h = current_time // 60
            start_m = current_time % 60
            end_h = (current_time + meeting_duration) // 60
            end_m = (current_time + meeting_duration) % 60
            
            start_time_str = f"{start_h:02d}:{start_m:02d}"
            end_time_str = f"{end_h:02d}:{end_m:02d}"
            
            print(f"Meeting scheduled on {day} from {start_time_str} to {end_time_str}")
            return

# Execute the function
find_meeting_time()