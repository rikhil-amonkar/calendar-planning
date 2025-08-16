from datetime import datetime, timedelta

def find_meeting_time(jack_schedule, charlotte_schedule, meeting_duration, preferred_end_time):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime(preferred_end_time, "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)

    # Convert string times to datetime objects
    jack_busy_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in jack_schedule]
    charlotte_busy_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in charlotte_schedule]

    current_time = work_start
    while current_time + meeting_duration <= work_end:
        available = True
        for start, end in jack_busy_times + charlotte_busy_times:
            if start <= current_time < end or start < current_time + meeting_duration <= end:
                available = False
                break
        if available:
            return f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}", "Monday"
        current_time += timedelta(minutes=15)  # Check every 15 minutes for availability

    return None, None

jack_schedule = [("09:30", "10:30"), ("11:00", "11:30"), ("12:30", "13:00"), ("14:00", "14:30"), ("16:00", "16:30")]
charlotte_schedule = [("09:30", "10:00"), ("10:30", "12:00"), ("12:30", "13:30"), ("14:00", "16:00")]
meeting_duration = 30  # in minutes
preferred_end_time = "17:00"

meeting_time, day_of_week = find_meeting_time(jack_schedule, charlotte_schedule, meeting_duration, preferred_end_time)
print(f"{meeting_time}, {day_of_week}")