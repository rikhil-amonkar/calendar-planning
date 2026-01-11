from datetime import datetime, timedelta

# Define work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define busy slots for each participant
busy_slots = {
    "Denise": [(datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Angela": [],
    "Natalie": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                (datetime.strptime("15:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Function to check if a time slot is free for all participants
def is_slot_free(slot_start, slot_end):
    for person, slots in busy_slots.items():
        for busy_start, busy_end in slots:
            if not (slot_end <= busy_start or slot_start >= busy_end):
                return False
    return True

# Find the earliest free slot
meeting_duration = timedelta(minutes=30)
current_time = work_start

while current_time + meeting_duration <= work_end:
    if is_slot_free(current_time, current_time + meeting_duration):
        break
    current_time += timedelta(minutes=15)  # Check every 15 minutes for a 30-minute slot

# Output the result
if current_time + meeting_duration <= work_end:
    start_time_str = current_time.strftime("%H:%M")
    end_time_str = (current_time + meeting_duration).strftime("%H:%M")
    print(f"Meeting time: {start_time_str}:{end_time_str} on Monday")
else:
    print("No available time slot found.")