from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, day, preferences):
    for start in range(9, 17, 30):
        if day == "Monday" and start > 14:  # Melissa does not want to meet on Monday after 14:00
            continue
        start_time = datetime.strptime(f"{day} {start:02d}:00", "%A %H:%M")
        end_time = start_time + timedelta(minutes=meeting_duration)
        if (start_time not in [datetime.strptime(f"{day} {s[0]:02d}:{s[0].minute:02d}", "%A %H:%M") for s in schedules]
                and end_time not in [datetime.strptime(f"{day} {s[1]:02d}:{s[1].minute:02d}", "%A %H:%M") for s in schedules]):
            return f"{start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')} on {day}"

    return "No available time found"

jeffrey_schedule = [
    (datetime.strptime("Monday 09:30", "%A %H:%M"), datetime.strptime("Monday 10:00", "%A %H:%M")),
    (datetime.strptime("Monday 10:30", "%A %H:%M"), datetime.strptime("Monday 11:00", "%A %H:%M")),
]

virginia_schedule = [
    (datetime.strptime("Monday 09:00", "%A %H:%M"), datetime.strptime("Monday 09:30", "%A %H:%M")),
    (datetime.strptime("Monday 10:00", "%A %H:%M"), datetime.strptime("Monday 10:30", "%A %H:%M")),
    (datetime.strptime("Monday 14:30", "%A %H:%M"), datetime.strptime("Monday 15:00", "%A %H:%M")),
    (datetime.strptime("Monday 16:00", "%A %H:%M"), datetime.strptime("Monday 16:30", "%A %H:%M")),
]

melissa_schedule = [
    (datetime.strptime("Monday 09:00", "%A %H:%M"), datetime.strptime("Monday 11:30", "%A %H:%M")),
    (datetime.strptime("Monday 12:00", "%A %H:%M"), datetime.strptime("Monday 12:30", "%A %H:%M")),
    (datetime.strptime("Monday 13:00", "%A %H:%M"), datetime.strptime("Monday 15:00", "%A %H:%M")),
    (datetime.strptime("Monday 16:00", "%A %H:%M"), datetime.strptime("Monday 17:00", "%A %H:%M")),
]

meeting_duration = 30
day = "Monday"
preferences = {
    "Melissa": ["after 14:00 on Monday"]
}

print(find_meeting_time(jeffrey_schedule + virginia_schedule + melissa_schedule, meeting_duration, day, preferences))