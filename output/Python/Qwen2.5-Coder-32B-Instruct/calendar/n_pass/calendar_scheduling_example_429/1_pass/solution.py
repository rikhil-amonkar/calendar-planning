from datetime import datetime, timedelta

# Define the workday start and end times
workday_start = datetime.strptime("09:00", "%H:%M")
workday_end = datetime.strptime("17:00", "%H:%M")

# Define the meeting duration
meeting_duration = timedelta(minutes=30)

# Define the busy times for each participant
busy_times = {
    "Judy": [(datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
             (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Olivia": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"))],
    "Eric": [],
    "Jacqueline": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                   (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Laura": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
              (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
              (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
              (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
              (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tyler": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
              (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
              (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
              (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
              (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Lisa": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
             (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
             (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
             (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
             (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
             (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Function to check if a time slot is free for all participants
def is_time_slot_free(time_slot, busy_times):
    for person, busy_periods in busy_times.items():
        for start, end in busy_periods:
            if not (time_slot[1] <= start or time_slot[0] >= end):
                return False
    return True

# Find a suitable time slot
current_time = workday_start
while current_time + meeting_duration <= workday_end:
    time_slot = (current_time, current_time + meeting_duration)
    if is_time_slot_free(time_slot, busy_times):
        break
    current_time += timedelta(minutes=30)

# Output the result
print(f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}:Monday")