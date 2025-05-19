from datetime import datetime, timedelta

# Define the meeting duration
meeting_duration = timedelta(hours=1)

# Define work hours
work_start = datetime.strptime("09:00", "%H:%M").time()
work_end = datetime.strptime("17:00", "%H:%M").time()

# Define existing schedules
martha_schedule = {
    "Monday": [(datetime.strptime("16:00", "%H:%M").time(), datetime.strptime("17:00", "%H:%M").time())],
    "Tuesday": [(datetime.strptime("15:00", "%H:%M").time(), datetime.strptime("15:30", "%H:%M").time())],
    "Wednesday": [(datetime.strptime("10:00", "%H:%M").time(), datetime.strptime("11:00", "%H:%M").time()),
                   (datetime.strptime("14:00", "%H:%M").time(), datetime.strptime("14:30", "%H:%M").time())]
}

beverly_schedule = {
    "Monday": [(datetime.strptime("09:00", "%H:%M").time(), datetime.strptime("13:30", "%H:%M").time()),
                (datetime.strptime("14:00", "%H:%M").time(), datetime.strptime("17:00", "%H:%M").time())],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M").time(), datetime.strptime("17:00", "%H:%M").time())],
    "Wednesday": [(datetime.strptime("09:30", "%H:%M").time(), datetime.strptime("15:30", "%H:%M").time()),
                   (datetime.strptime("16:30", "%H:%M").time(), datetime.strptime("17:00", "%H:%M").time())]
}

def is_time_available(schedule, day, start_time, duration):
    end_time = (datetime.combine(datetime.today(), start_time) + duration).time()
    for (start, end) in schedule.get(day, []):
        if start_time < end and end_time > start:
            return False
    return True

def find_meeting_time():
    for day in ["Monday", "Tuesday", "Wednesday"]:
        for hour in range(work_start.hour, work_end.hour):
            start_time = datetime.strptime(f"{hour}:00", "%H:%M").time()
            if is_time_available(martha_schedule, day, start_time, meeting_duration) and \
               is_time_available(beverly_schedule, day, start_time, meeting_duration):
                return f"{day}: {start_time.strftime('%H:%M')} to {(datetime.combine(datetime.today(), start_time) + meeting_duration).time().strftime('%H:%M')}"

meeting_time = find_meeting_time()
print(meeting_time)