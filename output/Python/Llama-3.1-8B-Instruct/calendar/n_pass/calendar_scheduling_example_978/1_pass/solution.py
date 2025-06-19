from datetime import datetime, timedelta

def find_meeting_time(brian_schedule, julia_schedule, duration, preference):
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']
    for day in days:
        if day == preference:
            continue
        for hour in range(9, 17):
            for minute in range(0, 60, 30):
                start_time = datetime.strptime(f'{day} {hour:02d}:{minute:02d}', '%A %H:%M')
                end_time = start_time + timedelta(minutes=duration)
                if (start_time, end_time) not in brian_schedule and (start_time, end_time) not in julia_schedule:
                    return f'{start_time.strftime("%H:%M")}-{end_time.strftime("%H:%M")}, {day}'

brian_schedule = [
    (datetime.strptime('Monday 09:30', '%A %H:%M'), datetime.strptime('Monday 10:00', '%A %H:%M')),
    (datetime.strptime('Monday 12:30', '%A %H:%M'), datetime.strptime('Monday 14:30', '%A %H:%M')),
    (datetime.strptime('Monday 15:30', '%A %H:%M'), datetime.strptime('Monday 16:00', '%A %H:%M')),
    (datetime.strptime('Tuesday 09:00', '%A %H:%M'), datetime.strptime('Tuesday 09:30', '%A %H:%M')),
    (datetime.strptime('Wednesday 12:30', '%A %H:%M'), datetime.strptime('Wednesday 14:00', '%A %H:%M')),
    (datetime.strptime('Wednesday 16:30', '%A %H:%M'), datetime.strptime('Wednesday 17:00', '%A %H:%M')),
    (datetime.strptime('Thursday 11:00', '%A %H:%M'), datetime.strptime('Thursday 11:30', '%A %H:%M')),
    (datetime.strptime('Thursday 13:00', '%A %H:%M'), datetime.strptime('Thursday 13:30', '%A %H:%M')),
    (datetime.strptime('Thursday 16:30', '%A %H:%M'), datetime.strptime('Thursday 17:00', '%A %H:%M')),
    (datetime.strptime('Friday 09:30', '%A %H:%M'), datetime.strptime('Friday 10:00', '%A %H:%M')),
    (datetime.strptime('Friday 10:30', '%A %H:%M'), datetime.strptime('Friday 11:00', '%A %H:%M')),
    (datetime.strptime('Friday 13:00', '%A %H:%M'), datetime.strptime('Friday 13:30', '%A %H:%M')),
    (datetime.strptime('Friday 15:00', '%A %H:%M'), datetime.strptime('Friday 16:00', '%A %H:%M')),
    (datetime.strptime('Friday 16:30', '%A %H:%M'), datetime.strptime('Friday 17:00', '%A %H:%M')),
]

julia_schedule = [
    (datetime.strptime('Monday 09:00', '%A %H:%M'), datetime.strptime('Monday 10:00', '%A %H:%M')),
    (datetime.strptime('Monday 11:00', '%A %H:%M'), datetime.strptime('Monday 11:30', '%A %H:%M')),
    (datetime.strptime('Monday 12:30', '%A %H:%M'), datetime.strptime('Monday 13:00', '%A %H:%M')),
    (datetime.strptime('Monday 15:30', '%A %H:%M'), datetime.strptime('Monday 16:00', '%A %H:%M')),
    (datetime.strptime('Tuesday 13:00', '%A %H:%M'), datetime.strptime('Tuesday 14:00', '%A %H:%M')),
    (datetime.strptime('Tuesday 16:00', '%A %H:%M'), datetime.strptime('Tuesday 16:30', '%A %H:%M')),
    (datetime.strptime('Wednesday 09:00', '%A %H:%M'), datetime.strptime('Wednesday 11:30', '%A %H:%M')),
    (datetime.strptime('Wednesday 12:00', '%A %H:%M'), datetime.strptime('Wednesday 12:30', '%A %H:%M')),
    (datetime.strptime('Wednesday 13:00', '%A %H:%M'), datetime.strptime('Wednesday 17:00', '%A %H:%M')),
    (datetime.strptime('Thursday 09:00', '%A %H:%M'), datetime.strptime('Thursday 10:30', '%A %H:%M')),
    (datetime.strptime('Thursday 11:00', '%A %H:%M'), datetime.strptime('Thursday 17:00', '%A %H:%M')),
    (datetime.strptime('Friday 09:00', '%A %H:%M'), datetime.strptime('Friday 10:00', '%A %H:%M')),
    (datetime.strptime('Friday 10:30', '%A %H:%M'), datetime.strptime('Friday 11:30', '%A %H:%M')),
    (datetime.strptime('Friday 12:30', '%A %H:%M'), datetime.strptime('Friday 14:00', '%A %H:%M')),
    (datetime.strptime('Friday 14:30', '%A %H:%M'), datetime.strptime('Friday 15:00', '%A %H:%M')),
    (datetime.strptime('Friday 15:30', '%A %H:%M'), datetime.strptime('Friday 16:00', '%A %H:%M')),
]

duration = 60
preference = 'Monday'

print(find_meeting_time(brian_schedule, julia_schedule, duration, preference))