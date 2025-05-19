from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, day):
    for start in range(9, 17, 30):
        start_time = datetime.strptime(f"{day} {start:02d}:00", "%A %H:%M")
        end_time = start_time + timedelta(minutes=meeting_duration)
        if (start_time not in [datetime.strptime(f"{day} {s[0]:02d}:{s[0].minute:02d}", "%A %H:%M") for s in schedules]
                and end_time not in [datetime.strptime(f"{day} {s[1]:02d}:{s[1].minute:02d}", "%A %H:%M") for s in schedules]):
            return f"{start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')} on {day}"

    return "No available time found"

katherine_schedule = [
    (datetime.strptime("Monday 12:00", "%A %H:%M"), datetime.strptime("Monday 12:30", "%A %H:%M")),
    (datetime.strptime("Monday 13:00", "%A %H:%M"), datetime.strptime("Monday 14:30", "%A %H:%M")),
]

rebecca_schedule = []

julie_schedule = [
    (datetime.strptime("Monday 09:00", "%A %H:%M"), datetime.strptime("Monday 09:30", "%A %H:%M")),
    (datetime.strptime("Monday 10:30", "%A %H:%M"), datetime.strptime("Monday 11:00", "%A %H:%M")),
    (datetime.strptime("Monday 13:30", "%A %H:%M"), datetime.strptime("Monday 14:00", "%A %H:%M")),
    (datetime.strptime("Monday 15:00", "%A %H:%M"), datetime.strptime("Monday 15:30", "%A %H:%M")),
]

angela_schedule = [
    (datetime.strptime("Monday 09:00", "%A %H:%M"), datetime.strptime("Monday 10:00", "%A %H:%M")),
    (datetime.strptime("Monday 10:30", "%A %H:%M"), datetime.strptime("Monday 11:00", "%A %H:%M")),
    (datetime.strptime("Monday 11:30", "%A %H:%M"), datetime.strptime("Monday 14:00", "%A %H:%M")),
    (datetime.strptime("Monday 14:30", "%A %H:%M"), datetime.strptime("Monday 15:00", "%A %H:%M")),
    (datetime.strptime("Monday 16:30", "%A %H:%M"), datetime.strptime("Monday 17:00", "%A %H:%M")),
]

nicholas_schedule = [
    (datetime.strptime("Monday 09:30", "%A %H:%M"), datetime.strptime("Monday 11:00", "%A %H:%M")),
    (datetime.strptime("Monday 11:30", "%A %H:%M"), datetime.strptime("Monday 13:30", "%A %H:%M")),
    (datetime.strptime("Monday 14:00", "%A %H:%M"), datetime.strptime("Monday 16:00", "%A %H:%M")),
    (datetime.strptime("Monday 16:30", "%A %H:%M"), datetime.strptime("Monday 17:00", "%A %H:%M")),
]

carl_schedule = [
    (datetime.strptime("Monday 09:00", "%A %H:%M"), datetime.strptime("Monday 11:00", "%A %H:%M")),
    (datetime.strptime("Monday 11:30", "%A %H:%M"), datetime.strptime("Monday 12:30", "%A %H:%M")),
    (datetime.strptime("Monday 13:00", "%A %H:%M"), datetime.strptime("Monday 14:30", "%A %H:%M")),
    (datetime.strptime("Monday 15:00", "%A %H:%M"), datetime.strptime("Monday 16:00", "%A %H:%M")),
    (datetime.strptime("Monday 16:30", "%A %H:%M"), datetime.strptime("Monday 17:00", "%A %H:%M")),
]

meeting_duration = 30
day = "Monday"

print(find_meeting_time(katherine_schedule + rebecca_schedule + julie_schedule + angela_schedule + nicholas_schedule + carl_schedule, meeting_duration, day))