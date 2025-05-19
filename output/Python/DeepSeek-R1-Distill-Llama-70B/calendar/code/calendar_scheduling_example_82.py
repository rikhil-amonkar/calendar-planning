def find_meeting_time():
    # Define the schedules for each person as a dictionary with days and busy intervals
    michael_schedule = {
        'Monday': [(9.5*60, 10.5*60), (15*60, 15.5*60), (16*60, 16.5*60)]
    }

    eric_schedule = {
        'Monday': []
    }

    arthur_schedule = {
        'Monday': [(9*60, 12*60), (13*60, 15*60), (15.5*60, 16*60), (16.5*60, 17*60)]
    }

    day = 'Monday'
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # 30 minutes

    # Combine all busy intervals
    busy_intervals = []
    for interval in michael_schedule[day]:
        busy_intervals.append((interval[0], interval[1], 'Michael'))
    for interval in eric_schedule[day]:
        busy_intervals.append((interval[0], interval[1], 'Eric'))
    for interval in arthur_schedule[day]:
        busy_intervals.append((interval[0], interval[1], 'Arthur'))

    # Sort busy intervals by start time
    busy_intervals.sort()

    # Find available slots
    current_time = start_time
    for busy_start, busy_end, person in busy_intervals:
        if current_time < busy_start:
            if busy_start - current_time >= meeting_duration:
                # Found a suitable time
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