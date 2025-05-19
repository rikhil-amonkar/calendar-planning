def find_meeting_time():
    # Define the busy intervals for Carl and Margaret for each day
    carl_schedule = {
        "Monday": [(11, 0, 11, 30)],
        "Tuesday": [(14, 30, 15, 0)],
        "Wednesday": [(10, 0, 11, 30), (13, 0, 13, 30)],
        "Thursday": [(13, 30, 14, 0), (16, 0, 16, 30)]
    }

    margaret_schedule = {
        "Monday": [(9, 0, 10, 30), (11, 0, 17, 0)],
        "Tuesday": [(9, 30, 12, 0), (13, 30, 14, 0), (15, 30, 17, 0)],
        "Wednesday": [(9, 30, 12, 0), (12, 30, 13, 0), (13, 30, 14, 30), (15, 0, 17, 0)],
        "Thursday": [(10, 0, 12, 0), (12, 30, 14, 0), (14, 30, 17, 0)]
    }

    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60   # 17:00 in minutes
    meeting_duration = 60  # 1 hour in minutes

    # Prioritize days, avoiding Thursday if possible
    priority_days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

    for day in priority_days:
        carl_busy = carl_schedule[day]
        margaret_busy = margaret_schedule[day]

        # Combine and sort busy intervals
        combined_busy = sorted(carl_busy + margaret_busy, key=lambda x: (x[0], x[1]))

        # Check for available slots
        current_time = start_time
        for interval in combined_busy:
            start, end = interval[0] * 60 + interval[1], interval[2] * 60 + interval[3]
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