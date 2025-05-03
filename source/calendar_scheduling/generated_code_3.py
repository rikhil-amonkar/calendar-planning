from datetime import datetime, timedelta

def find_meeting_time(start, end, duration, schedules):
    for hour in range(start.hour, end.hour):
        for minute in range(0, 60, duration):
            time = datetime(start.year, start.month, start.day, hour, minute)
            if all(time + timedelta(minutes=duration) < end and
                   time + timedelta(minutes=duration) not in schedule
                   for schedule in schedules.values()):
                return time.strftime('%H:%M'), (time + timedelta(minutes=duration)).strftime('%H:%M')
    return None

schedules = {
    'Stephen': [datetime(2024, 7, 22, 9, 30), datetime(2024, 7, 22, 10, 0),
                datetime(2024, 7, 22, 10, 30), datetime(2024, 7, 22, 16, 0),
                datetime(2024, 7, 22, 17, 0)],
    'Jacqueline': [],
    'Logan': [],
    'Larry': [datetime(2024, 7, 22, 9, 30), datetime(2024, 7, 22, 10, 0),
              datetime(2024, 7, 22, 15, 0), datetime(2024, 7, 22, 15, 30)],
    'Jean': [datetime(2024, 7, 22, 9, 30), datetime(2024, 7, 22, 12, 0),
             datetime(2024, 7, 22, 13, 0), datetime(2024, 7, 22, 13, 30),
             datetime(2024, 7, 22, 14, 0), datetime(2024, 7, 22, 14, 30),
             datetime(2024, 7, 22, 15, 0), datetime(2024, 7, 22, 15, 30)],
    'Adam': [datetime(2024, 7, 22, 9, 0), datetime(2024, 7, 22, 12, 30),
             datetime(2024, 7, 22, 13, 30), datetime(2024, 7, 22, 15, 0)],
    'Eugene': [datetime(2024, 7, 22, 9, 0), datetime(2024, 7, 22, 12, 0),
               datetime(2024, 7, 22, 12, 30), datetime(2024, 7, 22, 15, 30),
               datetime(2024, 7, 22, 16, 0), datetime(2024, 7, 22, 16, 30),
               datetime(2024, 7, 22, 17, 0)]
}

start = datetime(2024, 7, 22, 9, 0)
end = datetime(2024, 7, 22, 17, 0)
duration = 30

meeting_time = find_meeting_time(start, end, duration, schedules)
if meeting_time:
    print(f"Proposed meeting time: {meeting_time[0]} - {meeting_time[1]}")
else:
    print("No meeting time found")
```

Output: