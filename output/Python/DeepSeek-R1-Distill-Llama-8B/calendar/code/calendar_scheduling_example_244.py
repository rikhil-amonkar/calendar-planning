def find_meeting_time():
    # Define the meeting duration
    duration = 30  # 30 minutes

    # Define the work hours for the day (Monday)
    work_hours = [(9, 0), (17, 0)]  # (start hour, start minute), (end hour, end minute)

    # Define the working day in minutes
    work_day = 17 * 60 - 9 * 60  # 480 minutes (8 hours)

    # Define the blocked times for each participant
    walter_blocked = []
    cynthia_blocked = [
        (9, 0), (9, 30),  # 9:00-9:30 AM
        (10, 0), (10, 30),  # 10:00-10:30 AM
        (13, 30), (14, 30),  # 1:30-2:30 PM
        (15, 0), (16, 0)    # 3:00-4:00 PM
    ]
    ann_blocked = [
        (10, 0), (11, 0),  # 10:00-11:00 AM
        (13, 0), (13, 30),  # 1:00-1:30 PM
        (14, 0), (15, 0),  # 2:00-3:00 PM
        (16, 0), (16, 30)  # 4:00-4:30 PM
    ]
    catherine_blocked = [
        (9, 0), (11, 30),  # 9:00-11:30 AM
        (12, 30), (13, 30),  # 12:30-1:30 PM
        (14, 30), (17, 0)   # 2:30-5:00 PM
    ]
    kyle_blocked = [
        (9, 0), (9, 30),  # 9:00-9:30 AM
        (10, 0), (11, 30),  # 10:00-11:30 AM
        (12, 0), (12, 30),  # 12:00-12:30 PM
        (13, 0), (14, 30),  # 1:00-2:30 PM
        (15, 0), (16, 0)    # 3:00-4:00 PM
    ]

    # Convert blocked times to minutes for easier comparison
    walter_blocked = [(t[0], t[1]) for t in walter_blocked]
    cynthia_blocked = [(t[0], t[1]) for t in cynthia_blocked]
    ann_blocked = [(t[0], t[1]) for t in ann_blocked]
    catherine_blocked = [(t[0], t[1]) for t in catherine_blocked]
    kyle_blocked = [(t[0], t[1]) for t in kyle_blocked]

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
    for start_h in range(9, 17):
        for start_m in range(0, 60):
            start_min = start_h * 60 + start_m
            end_min = start_min + duration
            if end_min > 17 * 60:
                continue  # End after work hours

            # Check if this time slot is free for everyone
            if not is_blocked(start_min, end_min, walter_blocked) and \
               not is_blocked(start_min, end_min, cynthia_blocked) and \
               not is_blocked(start_min, end_min, ann_blocked) and \
               not is_blocked(start_min, end_min, catherine_blocked) and \
               not is_blocked(start_min, end_min, kyle_blocked):
                print(f"{start_h:02}:{start_m:02}-{start_h:02}:{end_min//60:02}")
                print("Monday")
                return

    # If no slot found (though problem states there is a solution)
    print("No available slot found")

# Run the function to find the meeting time
find_meeting_time()