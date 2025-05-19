from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, days, constraints):
    for day in days:
        if day == "Monday" and "Nicholas" in constraints:  # Nicholas does not want to meet on Monday
            continue
        if day == "Tuesday" and "Bryan" in constraints:  # Bryan does not want to meet on Tuesday
            continue
        if day == "Thursday" and "Nicholas" in constraints:  # Nicholas does not want to meet on Thursday
            continue
        for start in range(9, 17, 30):
            start_time = datetime.strptime(f"{day} {start:02d}:00", "%A %H:%M")
            end_time = start_time + timedelta(minutes=meeting_duration)
            if (start_time not in [datetime.strptime(f"{day} {s[0]:02d}:{s[0].minute:02d}", "%A %H:%M") for s in schedules]
                    and end_time not in [datetime.strptime(f"{day} {s[1]:02d}:{s[1].minute:02d}", "%A %H:%M") for s in schedules]):
                return f"{start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')} on {day}"

    return "No available time found"

bryan_schedule = [
    (datetime.strptime("Thursday 09:30", "%A %H:%M"), datetime.strptime("Thursday 10:00", "%A %H:%M")),
    (datetime.strptime("Thursday 12:30", "%A %H:%M"), datetime.strptime("Thursday 13:00", "%A %H:%M")),
    (datetime.strptime("Friday 10:30", "%A %H:%M"), datetime.strptime("Friday 11:00", "%A %H:%M")),
    (datetime.strptime("Friday 14:00", "%A %H:%M"), datetime.strptime("Friday 14:30", "%A %H:%M")),
]

nicholas_schedule = [
    (datetime.strptime("Monday 11:30", "%A %H:%M"), datetime.strptime("Monday 12:00", "%A %H:%M")),
    (datetime.strptime("Monday 13:00", "%A %H:%M"), datetime.strptime("Monday 15:30", "%A %H:%M")),
    (datetime.strptime("Tuesday 09:00", "%A %H:%M"), datetime.strptime("Tuesday 09:30", "%A %H:%M")),
    (datetime.strptime("Tuesday 11:00", "%A %H:%M"), datetime.strptime("Tuesday 13:30", "%A %H:%M")),
    (datetime.strptime("Tuesday 14:00", "%A %H:%M"), datetime.strptime("Tuesday 16:30", "%A %H:%M")),
    (datetime.strptime("Wednesday 09:00", "%A %H:%M"), datetime.strptime("Wednesday 09:30", "%A %H:%M")),
    (datetime.strptime("Wednesday 10:00", "%A %H:%M"), datetime.strptime("Wednesday 11:00", "%A %H:%M")),
    (datetime.strptime("Wednesday 11:30", "%A %H:%M"), datetime.strptime("Wednesday 13:30", "%A %H:%M")),
    (datetime.strptime("Wednesday 14:00", "%A %H:%M"), datetime.strptime("Wednesday 14:30", "%A %H:%M")),
    (datetime.strptime("Wednesday 15:00", "%A %H:%M"), datetime.strptime("Wednesday 16:30", "%A %H:%M")),
    (datetime.strptime("Thursday 10:30", "%A %H:%M"), datetime.strptime("Thursday 11:30", "%A %H:%M")),
    (datetime.strptime("Thursday 12:00", "%A %H:%M"), datetime.strptime("Thursday 12:30", "%A %H:%M")),
    (datetime.strptime("Thursday 15:00", "%A %H:%M"), datetime.strptime("Thursday 15:30", "%A %H:%M")),
    (datetime.strptime("Thursday 16:30", "%A %H:%M"), datetime.strptime("Thursday 17:00", "%A %H:%M")),
    (datetime.strptime("Friday 09:00", "%A %H:%M"), datetime.strptime("Friday 10:30", "%A %H:%M")),
    (datetime.strptime("Friday 11:00", "%A %H:%M"), datetime.strptime("Friday 12:00", "%A %H:%M")),
    (datetime.strptime("Friday 12:30", "%A %H:%M"), datetime.strptime("Friday 14:30", "%A %H:%M")),
    (datetime.strptime("Friday 15:30", "%A %H:%M"), datetime.strptime("Friday 16:00", "%A %H:%M")),
    (datetime.strptime("Friday 16:30", "%A %H:%M"), datetime.strptime("Friday 17:00", "%A %H:%M")),
]

meeting_duration = 60
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
constraints = {"Bryan": ["Tuesday"], "Nicholas": ["Monday", "Thursday"]}

print(find_meeting_time(bryan_schedule + nicholas_schedule, meeting_duration, days, constraints))