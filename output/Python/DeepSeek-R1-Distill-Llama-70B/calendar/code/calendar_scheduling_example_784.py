def find_meeting_time():
    # Define the schedules for each participant in decimal hours
    schedules = {
        'Judith': {
            'Monday': [(12.0, 12.5)],
            'Wednesday': [(11.5, 12.0)]
        },
        'Timothy': {
            'Monday': [(9.5, 10.0), (10.5, 11.5), (12.5, 14.0), (15.5, 17.0)],
            'Tuesday': [(9.5, 13.0), (13.5, 14.0), (14.5, 17.0)],
            'Wednesday': [(9.0, 9.5), (10.5, 11.0), (13.5, 14.5), (15.0, 15.5), (16.0, 16.5)]
        }
    }

    # Work hours in decimal
    start_time = 9.0
    end_time = 17.0

    # Days to check
    days = ['Monday', 'Tuesday', 'Wednesday']

    # Judith's preferences
    judith_preferred_days = ['Tuesday', 'Wednesday']
    judith_latest_start = 12.0  # 12:00 on Wednesday

    # Iterate through each day
    for day in days:
        # Skip Monday due to Judith's preference
        if day == 'Monday':
            continue

        # Iterate through possible start times in 1-hour increments
        for hour in range(9, 17):
            for minute in [0, 30]:
                start = hour + minute / 60.0
                end = start + 1.0  # 1-hour meeting

                # Ensure the meeting doesn't go beyond work hours and respects Judith's preferences
                if end > end_time:
                    continue
                if day == 'Wednesday' and start < judith_latest_start:
                    continue

                # Check if both participants are free during this slot
                all_free = True
                for name, calendar in schedules.items():
                    if day in calendar:
                        for busy_start, busy_end in calendar[day]:
                            # Check for overlap
                            if not (end <= busy_start or start >= busy_end):
                                all_free = False
                                break
                        if not all_free:
                            break

                if all_free:
                    # Format the time as HH:MM:HH:MM
                    start_h = int(start)
                    start_m = int((start - start_h) * 60)
                    end_h = int(end)
                    end_m = int((end - end_h) * 60)
                    return f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d} on {day}"

    # If no slot found (though problem states there is a solution)
    return "No available slot found"

# Execute the function
meeting_time = find_meeting_time()
print(meeting_time)