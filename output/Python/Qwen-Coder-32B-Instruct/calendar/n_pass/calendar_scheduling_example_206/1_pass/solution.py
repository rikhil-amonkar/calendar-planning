from datetime import datetime, timedelta

# Define the work hours
start_time = datetime.strptime("09:00", "%H:%M")
end_time = datetime.strptime("17:00", "%H:%M")

# Define the participants' schedules
schedules = {
    "Shirley": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M"))],
    "Jacob": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
              (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
              (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
              (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
              (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    "Stephen": [(datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M"))],
    "Margaret": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                 (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                 (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                 (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                 (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Mason": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
              (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
              (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
              (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
              (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
              (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Meeting duration
meeting_duration = timedelta(minutes=30)

# Margaret's preference
margaret_preference_start = datetime.strptime("14:30", "%H:%M")

# Find a suitable time slot
current_time = start_time
while current_time + meeting_duration <= end_time:
    available = True
    for person, schedule in schedules.items():
        if person == "Margaret" and current_time < margaret_preference_start:
            available = False
            break
        for busy_start, busy_end in schedule:
            if busy_start <= current_time < busy_end or busy_start < current_time + meeting_duration <= busy_end:
                available = False
                break
        if not available:
            break
    if available:
        print(f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}, Monday")
        break
    current_time += timedelta(minutes=30)