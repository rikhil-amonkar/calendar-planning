def find_meeting_time(judy_schedule, nicole_schedule, meeting_duration, preferred_start_time):
    from datetime import datetime, timedelta

    # Convert times to datetime objects for easier manipulation
    def parse_time(time_str):
        return datetime.strptime(time_str, "%H:%M")

    # Work hours
    start_of_day = parse_time("09:00")
    end_of_day = parse_time("17:00")

    # Meeting duration
    meeting_timedelta = timedelta(minutes=meeting_duration)

    # Nicole's available times
    nicole_busy_times = [(parse_time("09:00"), parse_time("10:00")), (parse_time("10:30"), parse_time("16:30"))]
    nicole_free_times = []

    # Calculate Nicole's free times
    current_time = start_of_day
    for busy_start, busy_end in nicole_busy_times:
        if current_time < busy_start:
            nicole_free_times.append((current_time, busy_start))
        current_time = max(current_time, busy_end)
    if current_time < end_of_day:
        nicole_free_times.append((current_time, end_of_day))

    # Filter free times based on Nicole's preference
    nicole_preferred_free_times = [time for time in nicole_free_times if time[0] >= parse_time(preferred_start_time)]

    # Find a common free time
    for start, end in nicole_preferred_free_times:
        if end - start >= meeting_timedelta:
            meeting_start = start.time().strftime("%H:%M")
            meeting_end = (start + meeting_timedelta).time().strftime("%H:%M")
            return f"{meeting_start}:{meeting_end} Monday"

    return "No suitable time found"

# Judy is free the entire day, so her schedule doesn't affect the calculation
judy_schedule = []
nicole_schedule = [("09:00", "10:00"), ("10:30", "16:30")]
meeting_duration = 30
preferred_start_time = "16:00"

print(find_meeting_time(judy_schedule, nicole_schedule, meeting_duration, preferred_start_time))