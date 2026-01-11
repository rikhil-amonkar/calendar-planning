def find_meeting_time():
    # Define the workday hours
    workday_start = 9 * 60  # 9:00 AM in minutes from midnight
    workday_end = 17 * 60   # 5:00 PM in minutes from midnight

    # Define each participant's busy periods in minutes from midnight
    busy_periods = {
        'Andrea': [],
        'Jack': [(9 * 60, 9 * 60 + 30), (14 * 60, 14 * 60 + 30)],
        'Madison': [(9 * 60 + 30, 10 * 60), (13 * 60, 14 * 60), (15 * 60, 15 * 60 + 30), (16 * 60 + 30, 17 * 60)],
        'Rachel': [(9 * 60 + 30, 10 * 60), (11 * 60, 11 * 60 + 30), (12 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60 + 30), (16 * 60, 17 * 60)],
        'Douglas': [(9 * 60, 11 * 60 + 30), (12 * 60, 16 * 60 + 30)],
        'Ryan': [(9 * 60, 9 * 60 + 30), (13 * 60, 14 * 60), (14 * 60 + 30, 17 * 60)]
    }

    # Function to check if a time slot is free for all participants
    def is_slot_free(slot_start, slot_end):
        for person, periods in busy_periods.items():
            for period_start, period_end in periods:
                if not (slot_end <= period_start or slot_start >= period_end):
                    return False
        return True

    # Iterate through the workday in 30-minute increments
    for start in range(workday_start, workday_end - 30 + 1, 30):
        end = start + 30
        if is_slot_free(start, end):
            # Convert start and end times back to HH:MM format
            start_time = f"{start // 60}:{start % 60:02}"
            end_time = f"{end // 60}:{end % 60:02}"
            print(f"Meeting time: {start_time}:{end_time} on Monday")
            return

# Run the function to find the meeting time
find_meeting_time()