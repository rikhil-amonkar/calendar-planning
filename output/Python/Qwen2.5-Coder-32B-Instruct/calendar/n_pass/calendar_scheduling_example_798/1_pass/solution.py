from datetime import datetime, timedelta

# Define the work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define the meeting duration
meeting_duration = timedelta(minutes=30)

# Define the participants' schedules
nancy_schedule = {
    "Monday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
               (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("13:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))]
}

jose_schedule = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                  (datetime.strptime("10:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                  (datetime.strptime("15:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Function to find available slots
def find_available_slots(schedule):
    available_slots = {}
    for day, booked_slots in schedule.items():
        current_time = work_start
        available_slots[day] = []
        for start, end in booked_slots:
            if current_time < start:
                available_slots[day].append((current_time, start))
            current_time = max(current_time, end)
        if current_time < work_end:
            available_slots[day].append((current_time, work_end))
    return available_slots

# Find available slots for both participants
nancy_available_slots = find_available_slots(nancy_schedule)
jose_available_slots = find_available_slots(jose_schedule)

# Find common available slots
common_available_slots = {}
for day in nancy_available_slots:
    if day in jose_available_slots:
        common_available_slots[day] = []
        for n_start, n_end in nancy_available_slots[day]:
            for j_start, j_end in jose_available_slots[day]:
                common_start = max(n_start, j_start)
                common_end = min(n_end, j_end)
                if common_start + meeting_duration <= common_end:
                    common_available_slots[day].append((common_start, common_start + meeting_duration))

# Find the earliest available slot
earliest_slot = None
for day, slots in common_available_slots.items():
    if slots:
        earliest_slot = slots[0]
        break

# Output the result
if earliest_slot:
    start_time, end_time = earliest_slot
    print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}, {day}")
else:
    print("No available slot found.")