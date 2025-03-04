from datetime import datetime, timedelta

# Define the start and end time of the workday
start_time = datetime.strptime('09:00', '%H:%M')
end_time = datetime.strptime('17:00', '%H:%M')

# Define the duration of the meeting
meeting_duration = timedelta(hours=0.5)

# Define the existing schedules for each participant
schedules = {
    'Raymond': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
                (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
                (datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
                (datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M'))],
    'Billy': [(datetime.strptime('10:00', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
              (datetime.strptime('12:00', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
              (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Donald': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
               (datetime.strptime('10:00', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
               (datetime.strptime('12:00', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
               (datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
               (datetime.strptime('16:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))]
}

# Find the first available time slot that is at least half an hour long and does not conflict with Billy's preference
for hour in range(start_time.hour, end_time.hour):
    for minute in range(start_time.minute, 60):
        time = datetime(year=2024, month=7, day=29, hour=hour, minute=minute)
        if time >= start_time and time + meeting_duration <= end_time:
            works_for_all = True
            for participant, schedule in schedules.items():
                for start, end in schedule:
                    if start <= time < end or start < time + meeting_duration <= end:
                        works_for_all = False
                        break
                if not works_for_all:
                    break
            if works_for_all and (hour < 15 or (hour == 15 and minute < 30)):
                print(f"Proposed time: {time.strftime('%H:%M')}-{(time + meeting_duration).strftime('%H:%M')}")
                break
    if works_for_all:
        break