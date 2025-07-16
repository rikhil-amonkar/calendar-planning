def find_meeting_time(participants_schedules, duration, work_hours_start, work_hours_end):
    # Convert all time slots to minutes since midnight for easier comparison
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration_min = duration * 60

    # Collect all busy intervals from all participants
    all_busy = []
    for schedule in participants_schedules.values():
        for interval in schedule:
            start, end = map(time_to_minutes, interval.split(' to '))
            all_busy.append((start, end))

    # Sort all busy intervals by start time
    all_busy.sort()

    # Check the time before the first busy interval
    if all_busy:
        first_busy_start = all_busy[0][0]
        available_start = work_start
        available_end = first_busy_start
        if available_end - available_start >= duration_min:
            return (minutes_to_time(available_start), 
                    minutes_to_time(available_start + duration_min))
    else:
        # No busy intervals at all - entire work day is available
        if work_end - work_start >= duration_min:
            return (minutes_to_time(work_start), 
                    minutes_to_time(work_start + duration_min))
        else:
            return None

    # Check gaps between busy intervals
    for i in range(len(all_busy) - 1):
        current_end = all_busy[i][1]
        next_start = all_busy[i+1][0]
        if next_start - current_end >= duration_min:
            # Found a suitable gap
            meeting_start = max(current_end, work_start)
            meeting_end = meeting_start + duration_min
            if meeting_end <= work_end:
                return (minutes_to_time(meeting_start), 
                        minutes_to_time(meeting_end))

    # Check the time after the last busy interval
    last_busy_end = all_busy[-1][1]
    available_start = last_busy_end
    available_end = work_end
    if available_end - available_start >= duration_min:
        return (minutes_to_time(available_start), 
                minutes_to_time(available_start + duration_min))

    return None

# Define participants' schedules
participants_schedules = {
    "Patrick": ["13:30 to 14:00", "14:30 to 15:00"],
    "Shirley": ["9:00 to 9:30", "11:00 to 11:30", "12:00 to 12:30", "14:30 to 15:00", "16:00 to 17:00"],
    "Jeffrey": ["9:00 to 9:30", "10:30 to 11:00", "11:30 to 12:00", "13:00 to 13:30", "16:00 to 17:00"],
    "Gloria": ["11:30 to 12:00", "15:00 to 15:30"],
    "Nathan": ["9:00 to 9:30", "10:30 to 12:00", "14:00 to 17:00"],
    "Angela": ["9:00 to 9:30", "10:00 to 11:00", "12:30 to 15:00", "15:30 to 16:30"],
    "David": ["9:00 to 9:30", "10:00 to 10:30", "11:00 to 14:00", "14:30 to 16:30"]
}

# Meeting parameters
meeting_duration = 30  # minutes
work_hours_start = "9:00"
work_hours_end = "17:00"
day_of_week = "Monday"

# Find meeting time
meeting_time = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end)

# Output the result
if meeting_time:
    start_time, end_time = meeting_time
    print(f"{{{start_time}:{end_time}}} {day_of_week}")
else:
    print("No suitable time found.")