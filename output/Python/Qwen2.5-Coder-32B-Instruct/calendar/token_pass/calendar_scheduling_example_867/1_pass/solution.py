from datetime import datetime, timedelta

# Define the work hours and meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Define the busy times for Betty and Scott
betty_busy = {
    "Monday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
               (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
               (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                  (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                  (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"))],
    "Thursday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                 (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                 (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                 (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                 (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

scott_busy = {
    "Monday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
               (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                  (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                  (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                  (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Thursday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                 (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                 (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                 (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                 (datetime.strptime("15:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                 (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Function to get available slots for a person
def get_available_slots(busy_times):
    available_slots = []
    current_time = work_start
    while current_time < work_end:
        next_slot = current_time + meeting_duration
        if next_slot > work_end:
            break
        is_free = True
        for start, end in busy_times:
            if start <= current_time < end or start < next_slot <= end or (current_time <= start and next_slot >= end):
                is_free = False
                current_time = end
                break
        if is_free:
            available_slots.append((current_time, next_slot))
            current_time = next_slot
        else:
            current_time += meeting_duration
    return available_slots

# Get available slots for Betty and Scott
betty_available = {}
scott_available = {}

for day in ["Monday", "Tuesday", "Wednesday", "Thursday"]:
    betty_available[day] = get_available_slots(betty_busy[day])
    scott_available[day] = get_available_slots(scott_busy[day])

# Find common free slots
common_slots = []
for day in ["Monday", "Tuesday", "Wednesday", "Thursday"]:
    if day == "Monday":
        continue  # Betty cannot meet on Monday
    for betty_slot in betty_available[day]:
        for scott_slot in scott_available[day]:
            if betty_slot[0] == scott_slot[0] and betty_slot[1] == scott_slot[1]:
                if day == "Wednesday":
                    continue  # Scott prefers not to have more meetings on Wednesday
                if day == "Thursday" and betty_slot[0] < datetime.strptime("15:00", "%H:%M"):
                    continue  # Meeting cannot be before 15:00 on Thursday
                common_slots.append((day, betty_slot[0], betty_slot[1]))

# Select the first suitable slot
if common_slots:
    day, start, end = common_slots[0]
    start_time_str = start.strftime("%H:%M")
    end_time_str = end.strftime("%H:%M")
    print(f"{start_time_str}:{end_time_str} {day}")
else:
    print("No suitable time found.")