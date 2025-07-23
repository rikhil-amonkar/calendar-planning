def find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end, day):
    # Convert all time strings to minutes since midnight for easier comparison
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration_minutes = meeting_duration * 60

    # Collect all busy intervals for all participants
    busy_intervals = []
    for schedule in participants_schedules:
        for interval in schedule:
            start, end = map(time_to_minutes, interval.split(' to '))
            busy_intervals.append((start, end))

    # Sort all busy intervals by start time
    busy_intervals.sort()

    # Find the earliest time after work_start where there's a gap of at least duration_minutes
    current_time = work_start
    for start, end in busy_intervals:
        if start > current_time and start - current_time >= duration_minutes:
            return f"{minutes_to_time(current_time)}:{minutes_to_time(current_time + duration_minutes)}"
        current_time = max(current_time, end)

    # Check the gap between the last meeting and work_end
    if work_end - current_time >= duration_minutes:
        return f"{minutes_to_time(current_time)}:{minutes_to_time(current_time + duration_minutes)}"

    return None

# Define the participants' schedules
michael_schedule = [
    "09:30 to 10:30",
    "15:00 to 15:30",
    "16:00 to 16:30"
]

eric_schedule = []  # Wide open

arthur_schedule = [
    "09:00 to 12:00",
    "13:00 to 15:00",
    "15:30 to 16:00",
    "16:30 to 17:00"
]

participants_schedules = [michael_schedule, eric_schedule, arthur_schedule]
meeting_duration = 0.5  # half an hour
work_hours_start = "09:00"
work_hours_end = "17:00"
day = "Monday"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end, day)

# Output the result
if meeting_time:
    print(f"{{{meeting_time}}} {day}")
else:
    print("No suitable time found.")