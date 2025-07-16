def find_meeting_time():
    # Define work hours and meeting duration
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes

    # Define days to consider
    days = ["Monday", "Tuesday", "Wednesday"]

    # Define John's constraints (no meetings after 14:30 on Monday)
    john_constraints = {
        "Monday": {"avoid_after": 14 * 60 + 30},  # 14:30 in minutes
        "Tuesday": {"avoid_after": work_end},     # No constraint (use work_end)
        "Wednesday": {"avoid_after": work_end},   # No constraint (use work_end)
    }

    # Define Jennifer's busy times for each day (in minutes since midnight)
    jennifer_busy = {
        "Monday": [
            (9 * 60, 11 * 60),      # 9:00-11:00
            (11 * 60 + 30, 13 * 60), # 11:30-13:00
            (13 * 60 + 30, 14 * 60 + 30), # 13:30-14:30
            (15 * 60, 17 * 60),      # 15:00-17:00
        ],
        "Tuesday": [
            (9 * 60, 11 * 60 + 30),  # 9:00-11:30
            (12 * 60, 17 * 60),      # 12:00-17:00
        ],
        "Wednesday": [
            (9 * 60, 11 * 60 + 30),  # 9:00-11:30
            (12 * 60, 12 * 60 + 30), # 12:00-12:30
            (13 * 60, 14 * 60),      # 13:00-14:00
            (14 * 60 + 30, 16 * 60), # 14:30-16:00
            (16 * 60 + 30, 17 * 60), # 16:30-17:00
        ],
    }

    # Iterate through each day to find a suitable time
    for day in days:
        # Get John's avoid-after time for the day
        avoid_after = john_constraints[day]["avoid_after"]
        # Jennifer's busy slots for the day
        busy_slots = jennifer_busy[day]

        # Start checking from work_start
        current_time = work_start

        # Iterate through Jennifer's busy slots to find gaps
        for start, end in busy_slots:
            if start > current_time:
                # Check if the gap is enough for the meeting
                gap_start = current_time
                gap_end = start
                # Ensure the gap is within John's constraints
                if gap_start + meeting_duration <= min(gap_end, avoid_after):
                    # Found a suitable time
                    meeting_start = gap_start
                    meeting_end = meeting_start + meeting_duration
                    # Format the time as HH:MM
                    start_str = f"{meeting_start // 60:02d}:{meeting_start % 60:02d}"
                    end_str = f"{meeting_end // 60:02d}:{meeting_end % 60:02d}"
                    return f"{day}: {start_str}:{end_str}"
            # Update current_time to the end of the busy slot
            current_time = max(current_time, end)

        # Check the time after the last busy slot
        if current_time + meeting_duration <= min(work_end, avoid_after):
            meeting_start = current_time
            meeting_end = meeting_start + meeting_duration
            # Format the time as HH:MM
            start_str = f"{meeting_start // 60:02d}:{meeting_start % 60:02d}"
            end_str = f"{meeting_end // 60:02d}:{meeting_end % 60:02d}"
            return f"{day}: {start_str}:{end_str}"

    return "No suitable time found."

# Run the function and print the result
print(find_meeting_time())