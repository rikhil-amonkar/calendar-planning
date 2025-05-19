def find_meeting_time():
    # Define the meeting duration
    duration = 30  # 30 minutes

    # Define the work hours for the day (Monday or Tuesday)
    work_hours = [(9, 0), (17, 0)]  # (start hour, start minute), (end hour, end minute)

    # Define the working day in minutes
    work_day = 17 * 60 - 9 * 60  # 480 minutes (8 hours)

    # Define the blocked times for each participant
    margaret_blocked = [
        # Monday
        ((10, 30), (11, 0)),
        ((11, 30), (12, 0)),
        ((13, 0), (13, 30)),
        ((15, 0), (17, 0)),
        # Tuesday
        ((12, 0), (12, 30))
    ]
    alexis_blocked = [
        # Monday
        ((9, 30), (11, 30)),
        ((12, 30), (13, 0)),
        ((14, 0), (17, 0)),
        # Tuesday
        ((9, 0), (9, 30)),
        ((10, 0), (10, 30)),
        ((14, 0), (16, 30))
    ]

    # Convert blocked times to minutes for easier comparison
    margaret_blocked = [(t[0], t[1]) for t in margaret_blocked]
    alexis_blocked = [(t[0], t[1]) for t in alexis_blocked]

    # Function to check if a time is blocked by a participant
    def is_blocked(start, end, participant):
        # Convert start and end to minutes
        start_min = start * 60
        end_min = end * 60
        # Check if the meeting time overlaps with any blocked time
        for block_start, block_end in participant:
            if (start_min < block_end and end_min > block_start):
                return True
        return False

    # Generate all possible start times within work hours
    for day in [0, 1]:  # 0=Monday, 1=Tuesday
        for start_h in range(9, 17):
            for start_m in range(0, 60):
                start_min = start_h * 60 + start_m
                end_min = start_min + duration
                if end_min > 17 * 60:
                    continue  # End after work hours

                # Check if this time slot is free for everyone
                if not is_blocked(start_min, end_min, margaret_blocked) and \
                   not is_blocked(start_min, end_min, alexis_blocked):
                    print(f"{start_h:02}:{start_m:02}-{start_h:02}:{end_min//60:02}")
                    print("Monday" if day == 0 else "Tuesday")
                    return

    # If no slot found (though problem states there is a solution)
    print("No available slot found")

# Run the function to find the meeting time
find_meeting_time()