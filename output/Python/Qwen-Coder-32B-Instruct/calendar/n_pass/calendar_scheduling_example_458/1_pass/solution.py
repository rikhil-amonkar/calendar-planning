from datetime import datetime, timedelta

# Define the workday start and end times
workday_start = datetime.strptime("09:00", "%H:%M")
workday_end = datetime.strptime("17:00", "%H:%M")

# Define the meeting duration
meeting_duration = timedelta(minutes=30)

# Define the participants' schedules
schedules = {
    "Wayne": [],
    "Melissa": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Catherine": [],
    "Gregory": [(datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Victoria": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                 (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                 (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                 (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                 (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Thomas": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Jennifer": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                 (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                 (datetime.strptime("11:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                 (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                 (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                 (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

# Wayne's preference to avoid meetings before 14:00
wayne_preference_start = datetime.strptime("14:00", "%H:%M")

# Function to check if a time slot is available for all participants
def is_time_slot_available(time_slot, schedules):
    for person, person_schedule in schedules.items():
        for event in person_schedule:
            if not (time_slot[1] <= event[0] or time_slot[0] >= event[1]):
                return False
    return True

# Find a suitable time slot
current_time = wayne_preference_start
while current_time + meeting_duration <= workday_end:
    time_slot = (current_time, current_time + meeting_duration)
    if is_time_slot_available(time_slot, schedules):
        break
    current_time += timedelta(minutes=30)

# Output the result
print(f"{time_slot[0].strftime('%H:%M')}:{time_slot[1].strftime('%H:%M')}:Monday")