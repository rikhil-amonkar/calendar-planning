def find_meeting_time():
    # Define the busy intervals for Nicole and Ruth for each day
    nicole_schedule = {
        "Monday": [(9, 0, 9, 30), (13, 0, 13, 30), (14, 30, 15, 30)],
        "Tuesday": [(9, 0, 9, 30), (11, 30, 13, 30), (14, 30, 15, 30)],
        "Wednesday": [(10, 0, 11, 0), (12, 30, 15, 0), (16, 0, 17, 0)]
    }

    ruth_schedule = {
        "Monday": [(9, 0, 17, 0)],
        "Tuesday": [(9, 0, 17, 0)],
        "Wednesday": [(9, 0, 10, 30), (11, 0, 11, 30), (12, 0, 12, 30), (13, 30, 15, 30), (16, 0, 16, 30)]
    }

    days = ["Monday", "Tuesday", "Wednesday"]
    start_time = 9 * 60  # 9:00 in minutes
    end_time = 17 * 60   # 17:00 in minutes
    meeting_duration = 30  # 30 minutes in minutes

    # Ruth's additional constraint: no meetings on Wednesday after 13:30
    ruth_constraint = {
        "Wednesday": (13, 30, 17, 0)
    }

    for day in days:
        nicole_busy = nicole_schedule[day]
        ruth_busy = ruth_schedule[day]

        # Apply Ruth's additional constraint for Wednesday
        if day == "Wednesday":
            ruth_busy += [ruth_constraint[day]]

        # Combine and sort busy intervals
        combined_busy = sorted(nicole_busy + ruth_busy, key=lambda x: (x[0], x[1]))

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