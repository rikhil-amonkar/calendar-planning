def find_meeting_time():
    # Define work hours and days to consider
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    days = ['Monday', 'Tuesday', 'Wednesday']
    meeting_duration = 60  # minutes

    # Define blocked times for each participant per day in minutes since midnight
    martha_blocked = {
        'Monday': [(16 * 60, 17 * 60)],
        'Tuesday': [(15 * 60, 15 * 60 + 30)],
        'Wednesday': [(10 * 60, 11 * 60), (14 * 60, 14 * 60 + 30)],
    }

    beverly_blocked = {
        'Monday': [(9 * 60, 13 * 60 + 30), (14 * 60, 17 * 60)],
        'Tuesday': [(9 * 60, 17 * 60)],
        'Wednesday': [(9 * 60 + 30, 15 * 60 + 30), (16 * 60 + 30, 17 * 60)],
    }

    # Iterate through each day to find a suitable time
    for day in days:
        # Combine all blocked times for the day and sort them
        blocked_times = martha_blocked.get(day, []) + beverly_blocked.get(day, [])
        blocked_times.sort()

        # Check the time before the first blocked period
        prev_end = work_start
        for start, end in blocked_times:
            if start - prev_end >= meeting_duration:
                # Found a suitable slot
                meeting_start = prev_end
                meeting_end = meeting_start + meeting_duration
                return day, f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
            prev_end = max(prev_end, end)

        # Check the time after the last blocked period
        if work_end - prev_end >= meeting_duration:
            meeting_start = prev_end
            meeting_end = meeting_start + meeting_duration
            return day, f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"

    return None, None

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

day, time_range = find_meeting_time()
print(f"{day}: {time_range}")