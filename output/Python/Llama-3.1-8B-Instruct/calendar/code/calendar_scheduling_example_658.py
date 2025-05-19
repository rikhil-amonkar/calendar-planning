from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, days, preferences):
    for day in days:
        for start in range(9, 17, 30):
            if day == "Tuesday" and start > 10:30 and "Shirley" in preferences:  # Shirley does not want to meet on Tuesday after 10:30
                continue
            start_time = datetime.strptime(f"{day} {start:02d}:00", "%A %H:%M")
            end_time = start_time + timedelta(minutes=meeting_duration)
            if (start_time not in [datetime.strptime(f"{day} {s[0]:02d}:{s[0].minute:02d}", "%A %H:%M") for s in schedules]
                    and end_time not in [datetime.strptime(f"{day} {s[1]:02d}:{s[1].minute:02d}", "%A %H:%M") for s in schedules]):
                return f"{start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')} on {day}"

    return "No available time found"

shirley_schedule = [
    (datetime.strptime("Monday 10:30", "%A %H:%M"), datetime.strptime("Monday 11:00", "%A %H:%M")),
    (datetime.strptime("Monday 12:00", "%A %H:%M"), datetime.strptime("Monday 12:30", "%A %H:%M")),
    (datetime.strptime("Monday 16:00", "%A %H:%M"), datetime.strptime("Monday 16:30", "%A %H:%M")),
    (datetime.strptime("Tuesday 09:30", "%A %H:%M"), datetime.strptime("Tuesday 10:00", "%A %H:%M")),
]

albert_schedule = [
    (datetime.strptime("Monday 09:00", "%A %H:%M"), datetime.strptime("Monday 17:00", "%A %H:%M")),
    (datetime.strptime("Tuesday 09:30", "%A %H:%M"), datetime.strptime("Tuesday 11:00", "%A %H:%M")),
    (datetime.strptime("Tuesday 11:30", "%A %H:%M"), datetime.strptime("Tuesday 12:30", "%A %H:%M")),
    (datetime.strptime("Tuesday 13:00", "%A %H:%M"), datetime.strptime("Tuesday 16:00", "%A %H:%M")),
    (datetime.strptime("Tuesday 16:30", "%A %H:%M"), datetime.strptime("Tuesday 17:00", "%A %H:%M")),
]

meeting_duration = 30
days = ["Monday", "Tuesday"]
preferences = {"Shirley": ["after 10:30 on Tuesday"]}

print(find_meeting_time(shirley_schedule + albert_schedule, meeting_duration, days, preferences))