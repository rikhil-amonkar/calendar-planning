from datetime import datetime, timedelta

# Define the work hours and meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Define the schedules for Nancy and Jose
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

# Function to find free slots
def find_free_slots(schedule):
    free_slots = {}
    for day, blocks in schedule.items():
        current_time = work_start
        day_free_slots = []
        for start, end in blocks:
            if current_time < start:
                day_free_slots.append((current_time, start))
            current_time = max(current_time, end)
        if current_time < work_end:
            day_free_slots.append((current_time, work_end))
        free_slots[day] = day_free_slots
    return free_slots

# Find free slots for Nancy and Jose
nancy_free_slots = find_free_slots(nancy_schedule)
jose_free_slots = find_free_slots(jose_schedule)

# Find common free slots
common_free_slots = {}
for day in nancy_free_slots:
    nancy_slots = nancy_free_slots[day]
    jose_slots = jose_free_slots[day]
    common_slots = []
    i, j = 0, 0
    while i < len(nancy_slots) and j < len(jose_slots):
        n_start, n_end = nancy_slots[i]
        j_start, j_end = jose_slots[j]
        overlap_start = max(n_start, j_start)
        overlap_end = min(n_end, j_end)
        if overlap_start < overlap_end and overlap_end - overlap_start >= meeting_duration:
            common_slots.append((overlap_start, overlap_end))
        if n_end <= j_end:
            i += 1
        else:
            j += 1
    common_free_slots[day] = common_slots

# Find the earliest available slot
earliest_slot = None
for day, slots in common_free_slots.items():
    if slots:
        earliest_slot = slots[0]
        break

# Output the result
if earliest_slot:
    start_time, end_time = earliest_slot
    print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')} {day}")
else:
    print("No available slot found.")