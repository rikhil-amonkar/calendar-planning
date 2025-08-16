from datetime import datetime, timedelta

# Define the workday and meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
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

# Function to check if a time slot is free for all participants
def is_time_slot_free(start_time, end_time):
    for person, times in busy_times.items():
        for busy_start, busy_end in times:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
    return True

# Find a suitable time slot
current_time = work_start
while current_time + meeting_duration <= work_end:
    if is_time_slot_free(current_time, current_time + meeting_duration):
        meeting_start = current_time.strftime("%H:%M")
        meeting_end = (current_time + meeting_duration).strftime("%H:%M")
        print(f"{meeting_start}:{meeting_end} Monday")
        break
    current_time += timedelta(minutes=30)