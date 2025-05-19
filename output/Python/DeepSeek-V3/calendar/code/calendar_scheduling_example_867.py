def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    meeting_duration = 30  # minutes

    # Betty's busy times in minutes since midnight for each day
    betty_busy = {
        'Monday': [(10*60, 10*60+30), (13*60+30, 14*60), (15*60, 15*60+30), (16*60, 16*60+30)],
        'Tuesday': [(9*60, 9*60+30), (11*60+30, 12*60), (12*60+30, 13*60), (13*60+30, 14*60), (16*60+30, 17*60)],
        'Wednesday': [(9*60+30, 10*60+30), (13*60, 13*60+30), (14*60, 14*60+30)],
        'Thursday': [(9*60+30, 10*60), (11*60+30, 12*60), (14*60, 14*60+30), (15*60, 15*60+30), (16*60+30, 17*60)]
    }

    # Scott's busy times in minutes since midnight for each day
    scott_busy = {
        'Monday': [(9*60+30, 15*60), (15*60+30, 16*60), (16*60+30, 17*60)],
        'Tuesday': [(9*60, 9*60+30), (10*60, 11*60), (11*60+30, 12*60), (12*60+30, 13*60+30), (14*60, 15*60), (16*60, 16*60+30)],
        'Wednesday': [(9*60+30, 12*60+30), (13*60, 13*60+30), (14*60, 14*60+30), (15*60, 15*60+30), (16*60, 16*60+30)],
        'Thursday': [(9*60, 9*60+30), (10*60, 10*60+30), (11*60, 12*60), (12*60+30, 13*60), (15*60, 16*60), (16*60+30, 17*60)]
    }

    # Additional constraints
    betty_no_days = ['Monday']  # Betty cannot meet on Monday
    betty_no_before = {'Tuesday': 15*60, 'Thursday': 15*60}  # Betty cannot meet before 15:00 on Tuesday and Thursday
    scott_avoid_day = 'Wednesday'  # Scott would like to avoid Wednesday

    # Iterate through each day to find a suitable time
    for day in days:
        if day in betty_no_days:
            continue
        if day == scott_avoid_day:
            continue

        # Get busy times for both participants on this day
        busy_times = betty_busy[day] + scott_busy[day]
        busy_times.sort()  # Sort by start time

        # Determine the earliest start time based on Betty's constraints
        day_start = work_start
        if day in betty_no_before:
            day_start = max(day_start, betty_no_before[day])

        # Initialize the previous end time as the start of the work day
        prev_end = day_start

        # Check for gaps between busy times
        for busy_start, busy_end in busy_times:
            if busy_start > prev_end:
                # Found a gap, check if it's long enough
                gap_start = prev_end
                gap_end = busy_start
                if gap_end - gap_start >= meeting_duration:
                    # Found a suitable time
                    start_time = gap_start
                    end_time = start_time + meeting_duration
                    # Format the time as HH:MM
                    start_str = f"{start_time // 60:02d}:{start_time % 60:02d}"
                    end_str = f"{end_time // 60:02d}:{end_time % 60:02d}"
                    print(f"{day}: {start_str}:{end_str}")
                    return
            # Update prev_end to the end of the current busy period
            prev_end = max(prev_end, busy_end)

        # Check the gap after the last busy period until the end of the work day
        if work_end - prev_end >= meeting_duration:
            start_time = prev_end
            end_time = start_time + meeting_duration
            start_str = f"{start_time // 60:02d}:{start_time % 60:02d}"
            end_str = f"{end_time // 60:02d}:{end_time % 60:02d}"
            print(f"{day}: {start_str}:{end_str}")
            return

    print("No suitable time found.")

find_meeting_time()