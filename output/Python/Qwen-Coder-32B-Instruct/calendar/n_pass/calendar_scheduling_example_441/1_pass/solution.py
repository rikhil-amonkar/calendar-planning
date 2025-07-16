from datetime import datetime, timedelta

# Define the workday start and end times
workday_start = datetime.strptime("09:00", "%H:%M")
workday_end = datetime.strptime("17:00", "%H:%M")

# Define the meeting duration
meeting_duration = timedelta(minutes=30)

# Define the existing schedules for each participant
schedules = {
    "Joan": [(datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
             (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    "Megan": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
              (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Austin": [],
    "Betty": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
              (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
              (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Judith": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    "Terry": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
              (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
              (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
              (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Kathryn": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                (datetime.strptime("11:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                (datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

def is_time_slot_free(time_slot, schedule):
    start, end = time_slot
    for busy_start, busy_end in schedule:
        if start < busy_end and end > busy_start:
            return False
    return True

def find_available_time_slot():
    current_time = workday_start
    while current_time + meeting_duration <= workday_end:
        time_slot = (current_time, current_time + meeting_duration)
        if all(is_time_slot_free(time_slot, schedule) for schedule in schedules.values()):
            return time_slot
        current_time += timedelta(minutes=15)  # Check every 15 minutes for availability
    return None

available_time_slot = find_available_time_slot()
if available_time_slot:
    start_time, end_time = available_time_slot
    print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}, Monday")
else:
    print("No available time slot found.")