from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, days):
    earliest_start = None
    for day in days:
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

nicole_schedule = [
    (datetime.strptime("Tuesday 16:00", "%A %H:%M"), datetime.strptime("Tuesday 16:30", "%A %H:%M")),
    (datetime.strptime("Wednesday 15:00", "%A %H:%M"), datetime.strptime("Wednesday 15:30", "%A %H:%M")),
    (datetime.strptime("Friday 12:00", "%A %H:%M"), datetime.strptime("Friday 12:30", "%A %H:%M")),
    (datetime.strptime("Friday 15:30", "%A %H:%M"), datetime.strptime("Friday 16:00", "%A %H:%M")),
]

daniel_schedule = [
    (datetime.strptime("Monday 09:00", "%A %H:%M"), datetime.strptime("Monday 12:30", "%A %H:%M")),
    (datetime.strptime("Monday 13:00", "%A %H:%M"), datetime.strptime("Monday 13:30", "%A %H:%M")),
    (datetime.strptime("Monday 14:00", "%A %H:%M"), datetime.strptime("Monday 16:30", "%A %H:%M")),
    (datetime.strptime("Tuesday 09:00", "%A %H:%M"), datetime.strptime("Tuesday 10:30", "%A %H:%M")),
    (datetime.strptime("Tuesday 11:30", "%A %H:%M"), datetime.strptime("Tuesday 12:30", "%A %H:%M")),
    (datetime.strptime("Tuesday 13:00", "%A %H:%M"), datetime.strptime("Tuesday 13:30", "%A %H:%M")),
    (datetime.strptime("Tuesday 15:00", "%A %H:%M"), datetime.strptime("Tuesday 16:00", "%A %H:%M")),
    (datetime.strptime("Tuesday 16:30", "%A %H:%M"), datetime.strptime("Tuesday 17:00", "%A %H:%M")),
    (datetime.strptime("Wednesday 09:00", "%A %H:%M"), datetime.strptime("Wednesday 10:00", "%A %H:%M")),
    (datetime.strptime("Wednesday 11:00", "%A %H:%M"), datetime.strptime("Wednesday 12:30", "%A %H:%M")),
    (datetime.strptime("Wednesday 13:00", "%A %H:%M"), datetime.strptime("Wednesday 13:30", "%A %H:%M")),
    (datetime.strptime("Wednesday 14:00", "%A %H:%M"), datetime.strptime("Wednesday 14:30", "%A %H:%M")),
    (datetime.strptime("Wednesday 16:30", "%A %H:%M"), datetime.strptime("Wednesday 17:00", "%A %H:%M")),
    (datetime.strptime("Thursday 11:00", "%A %H:%M"), datetime.strptime("Thursday 12:00", "%A %H:%M")),
    (datetime.strptime("Thursday 13:00", "%A %H:%M"), datetime.strptime("Thursday 14:00", "%A %H:%M")),
    (datetime.strptime("Thursday 15:00", "%A %H:%M"), datetime.strptime("Thursday 15:30", "%A %H:%M")),
    (datetime.strptime("Friday 10:00", "%A %H:%M"), datetime.strptime("Friday 11:00", "%A %H:%M")),
    (datetime.strptime("Friday 11:30", "%A %H:%M"), datetime.strptime("Friday 12:00", "%A %H:%M")),
    (datetime.strptime("Friday 12:30", "%A %H:%M"), datetime.strptime("Friday 14:30", "%A %H:%M")),
    (datetime.strptime("Friday 15:00", "%A %H:%M"), datetime.strptime("Friday 15:30", "%A %H:%M")),
    (datetime.strptime("Friday 16:00", "%A %H:%M"), datetime.strptime("Friday 16:30", "%A %H:%M")),
]

meeting_duration = 60
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

print(find_meeting_time(nicole_schedule + daniel_schedule, meeting_duration, days))