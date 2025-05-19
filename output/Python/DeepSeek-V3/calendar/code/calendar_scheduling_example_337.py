def find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end):
    # Convert time strings to minutes since start of day for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration = meeting_duration * 60

    # Initialize the list of busy intervals for all participants
    busy_intervals = []
    for schedule in participants_schedules:
        for interval in schedule:
            start, end = map(time_to_minutes, interval.split(':'))
            busy_intervals.append((start, end))

    # Sort all busy intervals by start time
    busy_intervals.sort()

    # Find the earliest time when everyone is free
    current_time = work_start
    for start, end in busy_intervals:
        if start > current_time:
            if start - current_time >= duration:
                return minutes_to_time(current_time), minutes_to_time(current_time + duration)
            else:
                current_time = end
        else:
            if end > current_time:
                current_time = end
        if current_time + duration > work_end:
            break

    # Check the remaining time after the last meeting
    if current_time + duration <= work_end:
        return minutes_to_time(current_time), minutes_to_time(current_time + duration)
    else:
        return None

# Define participants' schedules
participants_schedules = [
    ["11:30:12:00", "14:00:14:30"],  # John
    ["12:00:12:30", "14:00:15:00", "15:30:16:00"],  # Megan
    [],  # Brandon
    ["09:00:09:30", "10:00:10:30", "11:00:14:30", "15:00:16:00", "16:30:17:00"],  # Kimberly
    ["10:00:11:00", "11:30:14:00", "15:00:15:30"],  # Sean
    ["09:00:09:30", "10:30:12:00", "13:00:14:30", "16:00:16:30"],  # Lori
]

meeting_duration = 0.5  # half an hour
work_hours_start = "09:00"
work_hours_end = "17:00"
day_of_week = "Monday"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end)

if meeting_time:
    start_time, end_time = meeting_time
    print(f"{start_time}:{end_time}")
    print(day_of_week)
else:
    print("No suitable time found.")