def find_meeting_time():
    # Define the schedules for each participant
    schedules = {
        'John': [(11.5, 12.0), (14.0, 14.5)],
        'Megan': [(12.0, 12.5), (14.0, 15.0), (15.5, 16.0)],
        'Brandon': [],
        'Kimberly': [(9.0, 9.5), (10.0, 10.5), (11.0, 14.5), (15.0, 16.0), (16.5, 17.0)],
        'Sean': [(10.0, 11.0), (11.5, 14.0), (15.0, 15.5)],
        'Lori': [(9.0, 9.5), (10.5, 12.0), (13.0, 14.5), (16.0, 16.5)]
    }

    # Define the start and end of work hours in decimal
    start_time = 9.0
    end_time = 17.0

    # Check each possible 30-minute slot
    for hour in range(9, 17):
        for minute in [0, 30]:
            start = hour + minute / 60.0
            end = start + 0.5
            if end > 17.0:
                continue

            # Check if all participants are free during this slot
            all_free = True
            for name, busy_times in schedules.items():
                for busy_start, busy_end in busy_times:
                    # Check if the slot overlaps with any busy time
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