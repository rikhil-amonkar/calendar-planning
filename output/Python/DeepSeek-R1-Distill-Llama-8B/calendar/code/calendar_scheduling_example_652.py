def find_meeting_time():
    # Define the meeting duration
    duration = 30  # 30 minutes

    # Define the work hours for the day (Monday or Tuesday)
    work_hours = [(9, 0), (17, 0)]  # (start hour, start minute), (end hour, end minute)

    # Define the working day in minutes
    work_day = 17 * 60 - 9 * 60  # 480 minutes (8 hours)

    # Define the blocked times for each participant
    jesse_blocked = [
        # Monday
        ((13, 0), (14, 0)),  # 1:00-2:00 PM
        ((14, 30), (15, 0)),  # 2:30-3:00 PM
        # Tuesday
        ((9, 0), (9, 30)),  # 9:00-9:30 AM
        ((13, 0), (13, 30)),  # 1:00-1:30 PM
        ((14, 0), (15, 0))    # 2:00-3:00 PM
    ]
    lawrence_blocked = [
        # Monday
        ((9, 0), (17, 0)),  # 9:00-5:00 PM
        # Tuesday
        ((9, 30), (10, 30)),  # 9:30-10:30 AM
        ((11, 30), (12, 30)),  # 11:30-12:30 PM
        ((13, 0), (13, 30)),  # 1:00-1:30 PM
        ((14, 30), (15, 0)),  # 2:30-3:00 PM
        ((15, 30), (16, 30))  # 3:30-4:30 PM
    ]

    # Convert blocked times to minutes for easier comparison
    jesse_blocked = [(t[0], t[1]) for t in jesse_blocked]
    lawrence_blocked = [(t[0], t[1]) for t in lawrence_blocked]

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
                if not is_blocked(start_min, end_min, jesse_blocked) and \
                   not is_blocked(start_min, end_min, lawrence_blocked):
                    print(f"{start_h:02}:{start_m:02}-{start_h:02}:{end_min//60:02}")
                    print("Monday" if day == 0 else "Tuesday")
                    return

    # If no slot found (though problem states there is a solution)
    print("No available slot found")

# Run the function to find the meeting time
find_meeting_time()