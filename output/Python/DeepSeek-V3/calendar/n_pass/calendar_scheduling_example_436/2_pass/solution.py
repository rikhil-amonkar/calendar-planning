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

    # Convert all participants' schedules to busy intervals in minutes
    all_busy = []
    for schedule in participants_schedules.values():
        participant_busy = []
        for interval in schedule:
            start, end = map(time_to_minutes, interval.split(' to '))
            participant_busy.append((start, end))
        all_busy.append(participant_busy)

    # Check each minute in the work day for availability
    for minute in range(work_start, work_end - duration_min + 1):
        meeting_end = minute + duration_min
        # Check if all participants are free during this window
        all_free = True
        for participant in all_busy:
            is_free = True
            for busy_start, busy_end in participant:
                if not (meeting_end <= busy_start or minute >= busy_end):
                    is_free = False
                    break
            if not is_free:
                all_free = False
                break
        
        if all_free:
            return (minutes_to_time(minute), minutes_to_time(meeting_end))

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