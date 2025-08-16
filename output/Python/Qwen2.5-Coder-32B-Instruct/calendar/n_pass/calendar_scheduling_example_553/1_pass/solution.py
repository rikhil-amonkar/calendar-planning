from datetime import datetime, timedelta

def find_meeting_time(eric_schedule, henry_schedule, meeting_duration, preferred_end_time):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime(preferred_end_time, "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)

    available_slots = []

    # Combine Eric and Henry's schedules into one list of busy times
    busy_times = sorted(eric_schedule + henry_schedule, key=lambda x: x[0])

    current_time = work_start

    for start, end in busy_times:
        if current_time < start:
            available_slots.append((current_time, start))
        current_time = max(current_time, end)

    if current_time < work_end:
        available_slots.append((current_time, work_end))

    for start, end in available_slots:
        if end - start >= meeting_duration:
            return f"{start.strftime('%H:%M')}:{(start + meeting_duration).strftime('%H:%M')}", "Monday"

eric_schedule = [
    (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
    (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M"))
]

henry_schedule = [
    (datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
    (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
    (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
    (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
    (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
    (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
]

meeting_time, day_of_week = find_meeting_time(eric_schedule, henry_schedule, 30, "10:00")
print(meeting_time, day_of_week)