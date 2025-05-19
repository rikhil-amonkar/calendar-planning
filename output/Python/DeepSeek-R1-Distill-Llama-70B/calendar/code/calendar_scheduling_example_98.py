def find_meeting_time():
    # Define the schedules for each participant in decimal hours
    schedules = {
        'Juan': [(9.0, 10.5), (15.5, 16.0)],
        'Marilyn': [(11.0, 11.5), (12.5, 13.0)],
        'Ronald': [(9.0, 10.5), (12.0, 12.5), (13.0, 13.5), (14.0, 16.5)]
    }

    # Work hours in decimal
    start_time = 9.0
    end_time = 17.0

    # Iterate through possible start times in 30-minute increments
    for hour in range(9, 17):
        for minute in [0, 30]:
            start = hour + minute / 60.0
            end = start + 0.5  # 30-minute meeting

            # Ensure the meeting doesn't go beyond work hours
            if end > end_time:
                continue

            # Check if all participants are free during this slot
            all_free = True
            for name, busy_times in schedules.items():
                for busy_start, busy_end in busy_times:
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
                return f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"

    # If no slot found (though problem states there is a solution)
    return "No available slot found"

# Execute the function
meeting_time = find_meeting_time()
print(f"Meeting scheduled for {meeting_time} on Monday.")