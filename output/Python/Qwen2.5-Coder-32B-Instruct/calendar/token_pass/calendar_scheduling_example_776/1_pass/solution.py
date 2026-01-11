def find_meeting_time(john_schedule, jennifer_schedule, meeting_duration):
    # Convert times to minutes from midnight for easier calculation
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    def minutes_to_time(minutes):
        hours = minutes // 60
        minutes = minutes % 60
        return f"{hours:02}:{minutes:02}"

    # Days of the week and their respective busy times
    days = ["Monday", "Tuesday", "Wednesday"]
    john_busy_times = {
        "Monday": [],
        "Tuesday": [],
        "Wednesday": []
    }
    jennifer_busy_times = {
        "Monday": [(time_to_minutes("09:00"), time_to_minutes("11:00")),
                   (time_to_minutes("11:30"), time_to_minutes("13:00")),
                   (time_to_minutes("13:30"), time_to_minutes("14:30")),
                   (time_to_minutes("15:00"), time_to_minutes("17:00"))],
        "Tuesday": [(time_to_minutes("09:00"), time_to_minutes("11:30")),
                    (time_to_minutes("12:00"), time_to_minutes("17:00"))],
        "Wednesday": [(time_to_minutes("09:00"), time_to_minutes("11:30")),
                      (time_to_minutes("12:00"), time_to_minutes("12:30")),
                      (time_to_minutes("13:00"), time_to_minutes("14:00")),
                      (time_to_minutes("14:30"), time_to_minutes("16:00")),
                      (time_to_minutes("16:30"), time_to_minutes("17:00"))]
    }

    # Convert John's preference to a constraint
    john_avoid_after_monday = time_to_minutes("14:30")

    # Define work hours in minutes from midnight
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")

    # Check each day for a suitable meeting time
    for day in days:
        # Merge John's and Jennifer's busy times
        busy_times = john_busy_times[day] + jennifer_busy_times[day]
        busy_times.sort()

        # Initialize variables to track free time slots
        current_time = work_start
        free_slots = []

        # Iterate through busy times to find free slots
        for start, end in busy_times:
            if current_time < start:
                free_slots.append((current_time, min(end, work_end)))
            current_time = max(current_time, end)

        # Check remaining time after last busy period
        if current_time < work_end:
            free_slots.append((current_time, work_end))

        # Look for a suitable slot in free slots
        for start, end in free_slots:
            if (end - start) >= meeting_duration:
                if day == "Monday" and start >= john_avoid_after_monday:
                    continue
                meeting_start = start
                meeting_end = meeting_start + meeting_duration
                return f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)} {day}"

    return "No suitable time found"

# Meeting duration in minutes
meeting_duration = 30

# Call the function and print the result
print(find_meeting_time({}, {}, meeting_duration))