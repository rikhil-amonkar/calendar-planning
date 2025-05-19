from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, days, preferences):
    for day in days:
        for start in range(9, 17, 30):
            if day == "Monday" and start > 14:  # Doris does not want to meet on Monday after 14:00
                continue
            start_time = datetime.strptime(f"{day} {start:02d}:00", "%A %H:%M")
            end_time = start_time + timedelta(minutes=meeting_duration)
            if (start_time not in [datetime.strptime(f"{day} {s[0]:02d}:{s[0].minute:02d}", "%A %H:%M") for s in schedules]
                    and end_time not in [datetime.strptime(f"{day} {s[1]:02d}:{s[1].minute:02d}", "%A %H:%M") for s in schedules]):
                return f"{start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')} on {day}"

    return "No available time found"

jean_schedule = [
    (datetime.strptime("Tuesday 11:30", "%A %H:%M"), datetime.strptime("Tuesday 12:00", "%A %H:%M")),
    (datetime.strptime("Tuesday 16:00", "%A %H:%M"), datetime.strptime("Tuesday 16:30", "%A %H:%M")),
]

doris_schedule = [
    (datetime.strptime("Monday 09:00", "%A %H:%M"), datetime.strptime("Monday 11:30", "%A %H:%M")),
    (datetime.strptime("Monday 12:00", "%A %H:%M"), datetime.strptime("Monday 12:30", "%A %H:%M")),
    (datetime.strptime("Monday 13:30", "%A %H:%M"), datetime.strptime("Monday 16:00", "%A %H:%M")),
    (datetime.strptime("Monday 16:30", "%A %H:%M"), datetime.strptime("Monday 17:00", "%A %H:%M")),
    (datetime.strptime("Tuesday 09:00", "%A %H:%M"), datetime.strptime("Tuesday 17:00", "%A %H:%M")),
]

meeting_duration = 30
days = ["Monday", "Tuesday"]
preferences = {
    "Doris": ["after 14:00 on Monday"]
}

print(find_meeting_time(jean_schedule + doris_schedule, meeting_duration, days, preferences))