from datetime import datetime, timedelta

# Define the work hours and meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)
day_of_week = "Monday"

# Define the busy slots for Lisa and Anthony
lisa_busy_slots = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                   (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                   (datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:00", "%H:%M"))]

anthony_busy_slots = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                      (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                      (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                      (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                      (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                      (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]

# Combine busy slots
all_busy_slots = lisa_busy_slots + anthony_busy_slots
# Sort busy slots by start time
all_busy_slots.sort(key=lambda x: x[0])

# Find available slots
available_start = work_start
for busy_start, busy_end in all_busy_slots:
    if available_start + meeting_duration <= busy_start:
        available_end = available_start + meeting_duration
        if available_end <= busy_start:
            print(f"{available_start.strftime('%H:%M')}:{available_end.strftime('%H:%M')}")
            print(day_of_week)
            break
    available_start = max(available_start, busy_end)

# If the end of the work day is reached and no slot has been found
if available_start + meeting_duration <= work_end:
    print(f"{available_start.strftime('%H:%M')}:{(available_start + meeting_duration).strftime('%H:%M')}")
    print(day_of_week)