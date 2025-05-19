from datetime import datetime, timedelta

def find_meeting_time(daniel_schedule, bradley_schedule, meeting_duration, preferences):
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    for day in days:
        if day not in preferences:
            continue

        daniel_busy = [start for start, end in daniel_schedule if start.date() == datetime.strptime(day, "%A").date()]
        bradley_busy = [start for start, end in bradley_schedule if start.date() == datetime.strptime(day, "%A").date()]

        start_time = datetime.strptime(day + " 09:00", "%A %H:%M")
        end_time = datetime.strptime(day + " 17:00", "%A %H:%M")

        while start_time < end_time:
            if start_time not in daniel_busy and start_time not in bradley_busy:
                end_time = start_time + timedelta(minutes=meeting_duration)
                if end_time not in daniel_busy and end_time not in bradley_busy:
                    return f"{start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')} on {day}"
            start_time += timedelta(minutes=30)

    return "No available time found"

daniel_schedule = [
    (datetime.strptime("Monday 09:30", "%A %H:%M"), datetime.strptime("Monday 10:30", "%A %H:%M")),
    (datetime.strptime("Monday 12:00", "%A %H:%M"), datetime.strptime("Monday 12:30", "%A %H:%M")),
    (datetime.strptime("Monday 13:00", "%A %H:%M"), datetime.strptime("Monday 14:00", "%A %H:%M")),
    (datetime.strptime("Monday 14:30", "%A %H:%M"), datetime.strptime("Monday 15:00", "%A %H:%M")),
    (datetime.strptime("Monday 15:30", "%A %H:%M"), datetime.strptime("Monday 16:00", "%A %H:%M")),
    (datetime.strptime("Tuesday 11:00", "%A %H:%M"), datetime.strptime("Tuesday 12:00", "%A %H:%M")),
    (datetime.strptime("Tuesday 13:00", "%A %H:%M"), datetime.strptime("Tuesday 13:30", "%A %H:%M")),
    (datetime.strptime("Tuesday 15:30", "%A %H:%M"), datetime.strptime("Tuesday 16:00", "%A %H:%M")),
    (datetime.strptime("Tuesday 16:30", "%A %H:%M"), datetime.strptime("Tuesday 17:00", "%A %H:%M")),
    (datetime.strptime("Wednesday 09:00", "%A %H:%M"), datetime.strptime("Wednesday 10:00", "%A %H:%M")),
    (datetime.strptime("Wednesday 14:00", "%A %H:%M"), datetime.strptime("Wednesday 14:30", "%A %H:%M")),
    (datetime.strptime("Thursday 10:30", "%A %H:%M"), datetime.strptime("Thursday 11:00", "%A %H:%M")),
    (datetime.strptime("Thursday 12:00", "%A %H:%M"), datetime.strptime("Thursday 13:00", "%A %H:%M")),
    (datetime.strptime("Thursday 14:30", "%A %H:%M"), datetime.strptime("Thursday 15:00", "%A %H:%M")),
    (datetime.strptime("Thursday 15:30", "%A %H:%M"), datetime.strptime("Thursday 16:00", "%A %H:%M")),
    (datetime.strptime("Friday 09:00", "%A %H:%M"), datetime.strptime("Friday 09:30", "%A %H:%M")),
    (datetime.strptime("Friday 11:30", "%A %H:%M"), datetime.strptime("Friday 12:00", "%A %H:%M")),
    (datetime.strptime("Friday 13:00", "%A %H:%M"), datetime.strptime("Friday 13:30", "%A %H:%M")),
    (datetime.strptime("Friday 16:30", "%A %H:%M"), datetime.strptime("Friday 17:00", "%A %H:%M")),
]

bradley_schedule = [
    (datetime.strptime("Monday 09:30", "%A %H:%M"), datetime.strptime("Monday 11:00", "%A %H:%M")),
    (datetime.strptime("Monday 11:30", "%A %H:%M"), datetime.strptime("Monday 12:00", "%A %H:%M")),
    (datetime.strptime("Monday 12:30", "%A %H:%M"), datetime.strptime("Monday 13:00", "%A %H:%M")),
    (datetime.strptime("Monday 14:00", "%A %H:%M"), datetime.strptime("Monday 15:00", "%A %H:%M")),
    (datetime.strptime("Tuesday 10:30", "%A %H:%M"), datetime.strptime("Tuesday 11:00", "%A %H:%M")),
    (datetime.strptime("Tuesday 12:00", "%A %H:%M"), datetime.strptime("Tuesday 13:00", "%A %H:%M")),
    (datetime.strptime("Tuesday 13:30", "%A %H:%M"), datetime.strptime("Tuesday 14:00", "%A %H:%M")),
    (datetime.strptime("Tuesday 15:30", "%A %H:%M"), datetime.strptime("Tuesday 16:30", "%A %H:%M")),
    (datetime.strptime("Wednesday 09:00", "%A %H:%M"), datetime.strptime("Wednesday 10:00", "%A %H:%M")),
    (datetime.strptime("Wednesday 11:00", "%A %H:%M"), datetime.strptime("Wednesday 13:00", "%A %H:%M")),
    (datetime.strptime("Wednesday 13:30", "%A %H:%M"), datetime.strptime("Wednesday 14:00", "%A %H:%M")),
    (datetime.strptime("Wednesday 14:30", "%A %H:%M"), datetime.strptime("Wednesday 17:00", "%A %H:%M")),
    (datetime.strptime("Thursday 09:00", "%A %H:%M"), datetime.strptime("Thursday 12:30", "%A %H:%M")),
    (datetime.strptime("Thursday 13:30", "%A %H:%M"), datetime.strptime("Thursday 14:00", "%A %H:%M")),
    (datetime.strptime("Thursday 14:30", "%A %H:%M"), datetime.strptime("Thursday 15:00", "%A %H:%M")),
    (datetime.strptime("Thursday 15:30", "%A %H:%M"), datetime.strptime("Thursday 16:30", "%A %H:%M")),
    (datetime.strptime("Friday 09:00", "%A %H:%M"), datetime.strptime("Friday 09:30", "%A %H:%M")),
    (datetime.strptime("Friday 10:00", "%A %H:%M"), datetime.strptime("Friday 12:30", "%A %H:%M")),
    (datetime.strptime("Friday 13:00", "%A %H:%M"), datetime.strptime("Friday 13:30", "%A %H:%M")),
    (datetime.strptime("Friday 14:00", "%A %H:%M"), datetime.strptime("Friday 14:30", "%A %H:%M")),
    (datetime.strptime("Friday 15:30", "%A %H:%M"), datetime.strptime("Friday 16:30", "%A %H:%M")),
]

meeting_duration = 30

preferences = {
    "Daniel": ["Wednesday", "Thursday"],
    "Bradley": ["Monday", "Tuesday before 12:00", "Friday"]
}

print(find_meeting_time(daniel_schedule, bradley_schedule, meeting_duration, preferences))