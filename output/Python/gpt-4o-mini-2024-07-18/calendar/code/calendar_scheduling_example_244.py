from datetime import datetime, timedelta

def find_meeting_time(participants, duration, work_hours):
    # Convert work hours to datetime objects
    work_start = datetime.strptime(work_hours[0], "%H:%M")
    work_end = datetime.strptime(work_hours[1], "%H:%M")
    
    # Generate all time slots within work hours
    time_slots = []
    current_time = work_start
    while current_time + timedelta(minutes=duration) <= work_end:
        time_slots.append(current_time)
        current_time += timedelta(minutes=30)  # Check every half hour
    
    # Check each time slot against each participant's schedule
    for meeting_time in time_slots:
        meeting_end = meeting_time + timedelta(minutes=duration)
        if all(not (meeting_time < busy_start < meeting_end or meeting_time < busy_end < meeting_end) 
               for busy_times in participants.values() 
               for busy_start, busy_end in busy_times):
            return meeting_time.strftime("%H:%M"), meeting_end.strftime("%H:%M")
    
    return None

# Existing schedules
participants = {
    'Walter': [],
    'Cynthia': [(datetime(2023, 10, 16, 9, 0), datetime(2023, 10, 16, 9, 30)),
                (datetime(2023, 10, 16, 10, 0), datetime(2023, 10, 16, 10, 30)),
                (datetime(2023, 10, 16, 13, 30), datetime(2023, 10, 16, 14, 30)),
                (datetime(2023, 10, 16, 15, 0), datetime(2023, 10, 16, 16, 0))],
    'Ann': [(datetime(2023, 10, 16, 10, 0), datetime(2023, 10, 16, 11, 0)),
            (datetime(2023, 10, 16, 13, 0), datetime(2023, 10, 16, 13, 30)),
            (datetime(2023, 10, 16, 14, 0), datetime(2023, 10, 16, 15, 0)),
            (datetime(2023, 10, 16, 16, 0), datetime(2023, 10, 16, 16, 30))],
    'Catherine': [(datetime(2023, 10, 16, 9, 0), datetime(2023, 10, 16, 11, 30)),
                  (datetime(2023, 10, 16, 12, 30), datetime(2023, 10, 16, 13, 30)),
                  (datetime(2023, 10, 16, 14, 30), datetime(2023, 10, 16, 17, 0))],
    'Kyle': [(datetime(2023, 10, 16, 9, 0), datetime(2023, 10, 16, 9, 30)),
             (datetime(2023, 10, 16, 10, 0), datetime(2023, 10, 16, 11, 30)),
             (datetime(2023, 10, 16, 12, 0), datetime(2023, 10, 16, 12, 30)),
             (datetime(2023, 10, 16, 13, 0), datetime(2023, 10, 16, 14, 30)),
             (datetime(2023, 10, 16, 15, 0), datetime(2023, 10, 16, 16, 0))]
}

meeting_duration = 30  # in minutes
work_hours = ["09:00", "17:00"]
day_of_week = "Monday"

meeting_start, meeting_end = find_meeting_time(participants, meeting_duration, work_hours)

print(f"{meeting_start}:{meeting_end}")
print(day_of_week)