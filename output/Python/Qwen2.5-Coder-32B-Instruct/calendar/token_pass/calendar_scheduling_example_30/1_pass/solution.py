from datetime import datetime, timedelta

# Define the work hours
start_time = datetime.strptime("09:00", "%H:%M")
end_time = datetime.strptime("17:00", "%H:%M")

# Define busy times for each participant
busy_times = {
    "Jeffrey": [
        (datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
        (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M"))
    ],
    "Virginia": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
        (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))
    ],
    "Melissa": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
        (datetime.strptime("13:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ]
}

# Function to find free slots for a participant
def find_free_slots(busy_times, start_time, end_time):
    current_time = start_time
    free_slots = []
    for busy_start, busy_end in busy_times:
        if current_time < busy_start:
            free_slots.append((current_time, busy_start))
        current_time = max(current_time, busy_end)
    if current_time < end_time:
        free_slots.append((current_time, end_time))
    return free_slots

# Find free slots for all participants
free_slots = {}
for participant, times in busy_times.items():
    free_slots[participant] = find_free_slots(times, start_time, end_time)

# Find common free slots
common_free_slots = free_slots["Jeffrey"]
for participant in ["Virginia", "Melissa"]:
    new_common_slots = []
    for slot in common_free_slots:
        for free_slot in free_slots[participant]:
            overlap_start = max(slot[0], free_slot[0])
            overlap_end = min(slot[1], free_slot[1])
            if overlap_end - overlap_start >= timedelta(minutes=30):
                new_common_slots.append((overlap_start, overlap_end))
    common_free_slots = new_common_slots

# Consider Melissa's preference
preferred_slot = None
for slot in common_free_slots:
    if slot[0] <= datetime.strptime("14:00", "%H:%M"):
        preferred_slot = slot
        break
else:
    preferred_slot = common_free_slots[0]

# Output the solution
start, end = preferred_slot
print(f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')}:Monday")