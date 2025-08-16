from datetime import datetime, timedelta

# Define the work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define the meeting duration
meeting_duration = timedelta(minutes=30)

# Define the schedules for Arthur and Michael
arthur_schedule = {
    "Monday": [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
               (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
               (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Tuesday": [(datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Wednesday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                  (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                  (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

michael_schedule = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
               (datetime.strptime("15:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Wednesday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M"))]
}

# Define the days to consider
days_to_consider = ["Monday", "Tuesday", "Wednesday"]

# Function to check if a time slot is available for both participants
def is_slot_available(slot, arthur_slots, michael_slots):
    for arthur_slot in arthur_slots:
        if not (slot[1] <= arthur_slot[0] or slot[0] >= arthur_slot[1]):
            return False
    for michael_slot in michael_slots:
        if not (slot[1] <= michael_slot[0] or slot[0] >= michael_slot[1]):
            return False
    return True

# Find the earliest available slot
for day in days_to_consider:
    if day == "Tuesday":
        continue  # Arthur cannot meet on Tuesday
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        slot = (current_time, current_time + meeting_duration)
        if is_slot_available(slot, arthur_schedule[day], michael_schedule[day]):
            start_time_str = slot[0].strftime("%H:%M")
            end_time_str = slot[1].strftime("%H:%M")
            print(f"{start_time_str}:{end_time_str} {day}")
            break
        current_time += timedelta(minutes=30)