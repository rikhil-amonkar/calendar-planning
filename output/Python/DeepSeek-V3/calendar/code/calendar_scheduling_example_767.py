def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_duration = 60  # minutes

    # Define blocked times for each participant per day in minutes since midnight
    martha_blocked = {
        'Monday': [(16 * 60, 17 * 60)],
        'Tuesday': [(15 * 60, 15 * 60 + 30)],
        'Wednesday': [(10 * 60, 11 * 60), (14 * 60, 14 * 60 + 30)]
    }

    beverly_blocked = {
        'Monday': [(9 * 60, 13 * 60 + 30), (14 * 60, 17 * 60)],
        'Tuesday': [(9 * 60, 17 * 60)],
        'Wednesday': [(9 * 60 + 30, 15 * 60 + 30), (16 * 60 + 30, 17 * 60)]
    }

    # Iterate through each day to find a suitable time slot
    for day in days:
        # Collect all blocked times for both participants
        blocked_times = martha_blocked.get(day, []) + beverly_blocked.get(day, [])
        blocked_times.sort()  # Sort by start time

        # Check available slots between work hours
        current_time = work_start
        for block_start, block_end in blocked_times:
            if current_time + meeting_duration <= block_start:
                # Found a suitable slot
                start_h = current_time // 60
                start_m = current_time % 60
                end_h = (current_time + meeting_duration) // 60
                end_m = (current_time + meeting_duration) % 60
                return day, f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
            # Update current_time to the end of the current block if it's later
            if block_end > current_time:
                current_time = block_end
        # Check after the last block
        if current_time + meeting_duration <= work_end:
            start_h = current_time // 60
            start_m = current_time % 60
            end_h = (current_time + meeting_duration) // 60
            end_m = (current_time + meeting_duration) % 60
            return day, f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"

    return "No suitable time found", ""

# Execute the function and print the result
day, time_slot = find_meeting_time()
print(f"{day}: {time_slot}")