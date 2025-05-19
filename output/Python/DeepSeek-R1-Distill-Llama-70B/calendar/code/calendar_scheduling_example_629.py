def find_meeting_time():
    # Define the work hours and meeting duration
    work_hours = {
        "start": 9 * 60,  # Convert hours to minutes
        "end": 17 * 60
    }
    duration = 30  # 30 minutes in minutes

    # Participants' schedules
    schedules = {
        "Margaret": {
            "Monday": [[10*60 + 30, 11*60], [11*60 + 30, 12*60], [13*60, 13*60 + 30], [15*60, 17*60]],
            "Tuesday": [[12*60, 12*60 + 30]]
        },
        "Alexis": {
            "Monday": [[9*60 + 30, 11*60 + 30], [12*60 + 30, 13*60], [14*60, 17*60]],
            "Tuesday": [[9*60, 9*60 + 30], [10*60, 10*60 + 30], [14*60, 16*60 + 30]]
        }
    }

    # Days to check (Margaret does not want to meet on Monday)
    days = ["Tuesday"]

    # Margaret's preference to not meet on Monday and Tuesday before 14:30
    preferred_start = 14 * 60 + 30  # 14:30 in minutes

    # Iterate through each day
    for day in days:
        # Get busy intervals for the current day
        margaret_busy = schedules["Margaret"].get(day, [])
        alexis_busy = schedules["Alexis"].get(day, [])

        # Combine busy intervals
        all_busy = margaret_busy + alexis_busy

        # Sort busy intervals by start time
        all_busy.sort(key=lambda x: x[0])

        # Check for available slots
        previous_end = work_hours["start"]
        for busy_start, busy_end in all_busy:
            if busy_start > previous_end:
                # Found a free slot
                start_time = previous_end
                end_time = start_time + duration
                if end_time <= work_hours["end"]:
                    # Check if the slot is after Margaret's preferred time
                    if start_time >= preferred_start:
                        # Convert minutes back to HH:MM format
                        start_hour = start_time // 60
                        start_minute = start_time % 60
                        end_hour = end_time // 60
                        end_minute = end_time % 60

                        return f"{start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d} on {day}"
            previous_end = max(previous_end, busy_end)

        # Check the last slot after all busy intervals
        if previous_end + duration <= work_hours["end"]:
            start_time = previous_end
            end_time = start_time + duration
            if start_time >= preferred_start:
                start_hour = start_time // 60
                start_minute = start_time % 60
                end_hour = end_time // 60
                end_minute = end_time % 60

                return f"{start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d} on {day}"

    # If no time found (should not happen as per the problem statement)
    return "No available time found"

# Execute the function
meeting_time = find_meeting_time()
print(meeting_time)