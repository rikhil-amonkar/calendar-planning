from datetime import datetime, timedelta

def find_meeting_time(jack_schedule, charlotte_schedule, preferred_end_time):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    meeting_duration = timedelta(minutes=30)

    jack_busy_times = [tuple(map(lambda x: datetime.strptime(x, "%H:%M"), t.split(" to "))) for t in jack_schedule]
    charlotte_busy_times = [tuple(map(lambda x: datetime.strptime(x, "%H:%M"), t.split(" to "))) for t in charlotte_schedule]

    current_time = work_start
    while current_time + meeting_duration <= work_end:
        if current_time.hour >= preferred_end_time.hour and current_time.minute >= preferred_end_time.minute:
            break
        
        is_free_jack = all(current_time < start or current_time + meeting_duration > end for start, end in jack_busy_times)
        is_free_charlotte = all(current_time < start or current_time + meeting_duration > end for start, end in charlotte_busy_times)

        if is_free_jack and is_free_charlotte:
            return f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}", "Monday"
        
        current_time += timedelta(minutes=15)

    return None, None

jack_schedule = ["9:30 to 10:30", "11:00 to 11:30", "12:30 to 13:00", "14:00 to 14:30", "16:00 to 16:30"]
charlotte_schedule = ["9:30 to 10:00", "10:30 to 12:00", "12:30 to 13:30", "14:00 to 16:00"]
preferred_end_time = datetime.strptime("12:30", "%H:%M")

meeting_time, day_of_week = find_meeting_time(jack_schedule, charlotte_schedule, preferred_end_time)
print(meeting_time, day_of_week)