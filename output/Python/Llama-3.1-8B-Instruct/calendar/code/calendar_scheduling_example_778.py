from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, days, constraints):
    for day in days:
        if day == "Tuesday" and "Susan" in constraints:  # Susan does not want to meet on Tuesday
            continue
        for start in range(9, 17, 30):
            if day == "Monday" and start > 16:  # Sandra does not want to meet on Monday after 16:00
                continue
            if day == "Wednesday" and "Sandra" in constraints:  # Sandra does not want to meet on Wednesday
                continue
            start_time = datetime.strptime(f"{day} {start:02d}:00", "%A %H:%M")
            end_time = start_time + timedelta(minutes=meeting_duration)
            if (start_time not in [datetime.strptime(f"{day} {s[0]:02d}:{s[0].minute:02d}", "%A %H:%M") for s in schedules]
                    and end_time not in [datetime.strptime(f"{day} {s[1]:02d}:{s[1].minute:02d}", "%A %H:%M") for s in schedules]):
                return f"{start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')} on {day}"

    return "No available time found"

susan_schedule = [
    (datetime.strptime("Monday 12:30", "%A %H:%M"), datetime.strptime("Monday 13:00", "%A %H:%M")),
    (datetime.strptime("Monday 13:30", "%A %H:%M"), datetime.strptime("Monday 14:00", "%A %H:%M")),
    (datetime.strptime("Tuesday 11:30", "%A %H:%M"), datetime.strptime("Tuesday 12:00", "%A %H:%M")),
    (datetime.strptime("Wednesday 09:30", "%A %H:%M"), datetime.strptime("Wednesday 10:30", "%A %H:%M")),
    (datetime.strptime("Wednesday 14:00", "%A %H:%M"), datetime.strptime("Wednesday 14:30", "%A %H:%M")),
    (datetime.strptime("Wednesday 15:30", "%A %H:%M"), datetime.strptime("Wednesday 16:30", "%A %H:%M")),
]

sandra_schedule = [
    (datetime.strptime("Monday 09:00", "%A %H:%M"), datetime.strptime("Monday 13:00", "%A %H:%M")),
    (datetime.strptime("Monday 14:00", "%A %H:%M"), datetime.strptime("Monday 15:00", "%A %H:%M")),
    (datetime.strptime("Monday 16:00", "%A %H:%M"), datetime.strptime("Monday 16:30", "%A %H:%M")),
    (datetime.strptime("Tuesday 09:00", "%A %H:%M"), datetime.strptime("Tuesday 09:30", "%A %H:%M")),
    (datetime.strptime("Tuesday 10:30", "%A %H:%M"), datetime.strptime("Tuesday 12:00", "%A %H:%M")),
    (datetime.strptime("Tuesday 12:30", "%A %H:%M"), datetime.strptime("Tuesday 13:30", "%A %H:%M")),
    (datetime.strptime("Tuesday 14:00", "%A %H:%M"), datetime.strptime("Tuesday 14:30", "%A %H:%M")),
    (datetime.strptime("Tuesday 16:00", "%A %H:%M"), datetime.strptime("Tuesday 17:00", "%A %H:%M")),
    (datetime.strptime("Wednesday 09:00", "%A %H:%M"), datetime.strptime("Wednesday 11:30", "%A %H:%M")),
    (datetime.strptime("Wednesday 12:00", "%A %H:%M"), datetime.strptime("Wednesday 12:30", "%A %H:%M")),
    (datetime.strptime("Wednesday 13:00", "%A %H:%M"), datetime.strptime("Wednesday 17:00", "%A %H:%M")),
]

meeting_duration = 30
days = ["Monday", "Tuesday", "Wednesday"]
constraints = {"Susan": ["Tuesday"], "Sandra": ["Monday after 16:00", "Wednesday"]}

print(find_meeting_time(susan_schedule + sandra_schedule, meeting_duration, days, constraints))