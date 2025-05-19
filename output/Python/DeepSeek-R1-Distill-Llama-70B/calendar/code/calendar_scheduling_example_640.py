def find_meeting_time():
    # Define the busy intervals for Bobby and Michael for each day
    bobby_schedule = {
        "Monday": [(14, 30, 15, 0)],
        "Tuesday": [(9, 0, 11, 30), (12, 0, 12, 30), (13, 0, 15, 0), (15, 30, 17, 0)]
    }

    michael_schedule = {
        "Monday": [(9, 0, 10, 0), (10, 30, 13, 30), (14, 0, 15, 0), (15, 30, 17, 0)],
        "Tuesday": [(9, 0, 10, 30), (11, 0, 11, 30), (12, 0, 14, 0), (15, 0, 16, 0), (16, 30, 17, 0)]
    }

    days = ["Monday", "Tuesday"]
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # 30 minutes in minutes

    for day in days:
        bobby_busy = bobby_schedule[day]
        michael_busy = michael_schedule[day]

        # Combine and sort busy intervals
        combined_busy = sorted(bobby_busy + michael_busy, key=lambda x: (x[0], x[1]))

        # Check for available slots
        current_time = start_time
        for busy_start, busy_end in combined_busy:
            start = busy_start[0] * 60 + busy_start[1]
            end = busy_end[0] * 60 + busy_end[1]
            if current_time + meeting_duration <= start:
                # Found a slot
                meeting_start = current_time
                meeting_end = meeting_start + meeting_duration
                return f"{meeting_start//60:02d}:{meeting_start%60:02d}:{meeting_end//60:02d}:{meeting_end%60:02d} on {day}"
            current_time = max(current_time, end)

        # Check if there's time after the last busy interval
        if current_time + meeting_duration <= end_time:
            meeting_start = current_time
            meeting_end = meeting_start + meeting_duration
            return f"{meeting_start//60:02d}:{meeting_start%60:02d}:{meeting_end//60:02d}:{meeting_end%60:02d} on {day}"

    return "No available time found"

print(find_meeting_time())