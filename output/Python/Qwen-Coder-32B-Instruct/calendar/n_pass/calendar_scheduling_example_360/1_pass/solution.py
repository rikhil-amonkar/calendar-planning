from datetime import datetime, timedelta

# Define the workday start and end times
workday_start = datetime.strptime("09:00", "%H:%M")
workday_end = datetime.strptime("17:00", "%H:%M")

# Define the meeting duration
meeting_duration = timedelta(minutes=30)

# Define the busy times for each participant
busy_times = {
    "Emily": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Mason": [],
    "Maria": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
              (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"))],
    "Carl": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
             (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
             (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
             (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
             (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "David": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
              (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
              (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
              (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Frank": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
              (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
              (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
              (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Function to check if a time slot is available for all participants
def is_time_slot_available(time_slot):
    for person, busy in busy_times.items():
        for busy_start, busy_end in busy:
            if busy_start <= time_slot[1] and busy_end >= time_slot[0]:
                return False
    return True

# Find a suitable time slot
current_time = workday_start
while current_time + meeting_duration <= workday_end:
    time_slot = (current_time, current_time + meeting_duration)
    if is_time_slot_available(time_slot):
        # Output the found time slot and day of the week
        print(f"{time_slot[0].strftime('%H:%M')}:{time_slot[1].strftime('%H:%M')}:Monday")
        break
    current_time += timedelta(minutes=30)