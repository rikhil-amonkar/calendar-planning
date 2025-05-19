from datetime import datetime, timedelta

# Define the meeting duration in hours
meeting_duration = timedelta(hours=1)

# Define the work hours and days
work_hours_start = datetime.strptime("09:00", "%H:%M")
work_hours_end = datetime.strptime("17:00", "%H:%M")

# Define participant schedules
patricia_schedule = {
    "Monday": [
        (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
        (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
        (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))
    ],
    "Tuesday": [
        (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
        (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
        (datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
        (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ]
}

jesse_schedule = {
    "Monday": [
        (work_hours_start, work_hours_end)  # Blocked all day
    ],
    "Tuesday": [
        (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
        (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
        (datetime.strptime("15:30", "%H:%M"), work_hours_end)  # Blocked until the end of day
    ]
}

def find_open_time(schedules, work_start, work_end, duration):
    for day in schedules.keys():
        busy_times = schedules[day]
        available_start = work_start

        for busy_start, busy_end in busy_times:
            if available_start + duration <= busy_start:
                return day, available_start, available_start + duration
            available_start = max(available_start, busy_end)

        if available_start + duration <= work_end:
            return day, available_start, available_start + duration

    return None, None, None

# Find available time slots
day, start_time, end_time = find_open_time(patricia_schedule['Monday'], work_hours_start, work_hours_end, meeting_duration)
if day is None:
    day, start_time, end_time = find_open_time(patricia_schedule['Tuesday'], work_hours_start, work_hours_end, meeting_duration)

# Output results
if day:
    print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')} - {day}")