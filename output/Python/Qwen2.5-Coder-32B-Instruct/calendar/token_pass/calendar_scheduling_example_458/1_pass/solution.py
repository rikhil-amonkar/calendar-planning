from datetime import datetime, timedelta

# Define the workday start and end times
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define Wayne's preferred start time
wayne_preferred_start = datetime.strptime("14:00", "%H:%M")

# Define each participant's busy times
busy_times = {
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

# Function to check if a time slot is free for all participants
def is_slot_free(slot_start, slot_end):
    for participant, times in busy_times.items():
        for busy_start, busy_end in times:
            # If the slot overlaps with any busy time, it's not free
            if not (slot_end <= busy_start or slot_start >= busy_end):
                return False
    return True

# Iterate over each possible 30-minute slot starting from Wayne's preferred time
current_time = wayne_preferred_start
while current_time + timedelta(minutes=30) <= work_end:
    next_time = current_time + timedelta(minutes=30)
    if is_slot_free(current_time, next_time):
        # Found a suitable slot
        meeting_time = f"{current_time.strftime('%H:%M')}:{next_time.strftime('%H:%M')}"
        meeting_day = "Monday"
        print(f"Meeting time: {meeting_time}, Day: {meeting_day}")
        break
    current_time += timedelta(minutes=30)