from datetime import datetime, timedelta

# Define the workday start and end times
workday_start = datetime.strptime("09:00", "%H:%M")
workday_end = datetime.strptime("17:00", "%H:%M")

# Define the meeting duration
meeting_duration = timedelta(minutes=30)

# Define the busy times for each participant
busy_times = {
    "Megan": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
              (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
              (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M"))],
    "Christine": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                  (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                  (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                  (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Gabriel": [],
    "Sara": [(datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
             (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    "Bruce": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
              (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
              (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
              (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
              (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Kathryn": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Billy": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
              (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
              (datetime.strptime("12:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
              (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M"))]
}

# Function to check if a time slot is free for all participants
def is_time_slot_free(time_slot):
    for participant, busy_slots in busy_times.items():
        for busy_slot in busy_slots:
            if not (time_slot[1] <= busy_slot[0] or time_slot[0] >= busy_slot[1]):
                return False
    return True

# Find a suitable time slot
current_time = workday_start
while current_time + meeting_duration <= workday_end:
    time_slot = (current_time, current_time + meeting_duration)
    if is_time_slot_free(time_slot):
        meeting_time = f"{time_slot[0].strftime('%H:%M')}:{time_slot[1].strftime('%H:%M')}"
        meeting_day = "Monday"
        break
    current_time += timedelta(minutes=30)

print(f"{meeting_time}:{meeting_day}")