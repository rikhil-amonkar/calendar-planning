from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, day):
    earliest_start = None
    for start in range(9, 17, 30):
        start_time = datetime.strptime(f"{day} {start:02d}:00", "%A %H:%M")
        end_time = start_time + timedelta(minutes=meeting_duration)
        if (start_time not in [datetime.strptime(f"{day} {s[0]:02d}:{s[0].minute:02d}", "%A %H:%M") for s in schedules]
                and end_time not in [datetime.strptime(f"{day} {s[1]:02d}:{s[1].minute:02d}", "%A %H:%M") for s in schedules]):
            if earliest_start is None or start_time < earliest_start:
                earliest_start = start_time
    if earliest_start is not None:
        end_time = earliest_start + timedelta(minutes=meeting_duration)
        return f"{earliest_start.strftime('%H:%M')} - {end_time.strftime('%H:%M')} on {earliest_start.strftime('%A')}"
    return "No available time found"

steven_schedule = []

roy_schedule = []

cynthia_schedule = [
    (datetime.strptime("Monday 09:30", "%A %H:%M"), datetime.strptime("Monday 10:30", "%A %H:%M")),
    (datetime.strptime("Monday 11:30", "%A %H:%M"), datetime.strptime("Monday 12:00", "%A %H:%M")),
    (datetime.strptime("Monday 13:00", "%A %H:%M"), datetime.strptime("Monday 13:30", "%A %H:%M")),
    (datetime.strptime("Monday 15:00", "%A %H:%M"), datetime.strptime("Monday 16:00", "%A %H:%M")),
]

lauren_schedule = [
    (datetime.strptime("Monday 09:00", "%A %H:%M"), datetime.strptime("Monday 09:30", "%A %H:%M")),
    (datetime.strptime("Monday 10:30", "%A %H:%M"), datetime.strptime("Monday 11:00", "%A %H:%M")),
    (datetime.strptime("Monday 11:30", "%A %H:%M"), datetime.strptime("Monday 12:00", "%A %H:%M")),
    (datetime.strptime("Monday 13:00", "%A %H:%M"), datetime.strptime("Monday 13:30", "%A %H:%M")),
    (datetime.strptime("Monday 14:00", "%A %H:%M"), datetime.strptime("Monday 14:30", "%A %H:%M")),
    (datetime.strptime("Monday 15:00", "%A %H:%M"), datetime.strptime("Monday 15:30", "%A %H:%M")),
    (datetime.strptime("Monday 16:00", "%A %H:%M"), datetime.strptime("Monday 17:00", "%A %H:%M")),
]

robert_schedule = [
    (datetime.strptime("Monday 10:30", "%A %H:%M"), datetime.strptime("Monday 11:00", "%A %H:%M")),
    (datetime.strptime("Monday 11:30", "%A %H:%M"), datetime.strptime("Monday 12:00", "%A %H:%M")),
    (datetime.strptime("Monday 12:30", "%A %H:%M"), datetime.strptime("Monday 13:30", "%A %H:%M")),
    (datetime.strptime("Monday 14:00", "%A %H:%M"), datetime.strptime("Monday 16:00", "%A %H:%M")),
]

meeting_duration = 30
day = "Monday"

print(find_meeting_time(steven_schedule + roy_schedule + cynthia_schedule + lauren_schedule + robert_schedule, meeting_duration, day))