from datetime import datetime, timedelta

# Define work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define busy times for Russell and Alexander
russell_busy = {
    "Monday": [datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")],
    "Tuesday": [datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")]
}

alexander_busy = {
    "Monday": [
        datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M"),
        datetime.strptime("12:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"),
        datetime.strptime("15:00", "%H:%M"), datetime.strptime("17:00", "%H:%M")
    ],
    "Tuesday": [
        datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M"),
        datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M"),
        datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"),
        datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M")
    ]
}

# Function to find free slots
def find_free_slots(busy_times, work_start, work_end):
    free_slots = []
    current_time = work_start
    for start, end in busy_times:
        if current_time < start:
            free_slots.append((current_time, start))
        current_time = max(current_time, end)
    if current_time < work_end:
        free_slots.append((current_time, work_end))
    return free_slots

# Find free slots for both participants
russell_free_monday = find_free_slots(russell_busy["Monday"], work_start, work_end)
russell_free_tuesday = find_free_slots(russell_busy["Tuesday"], work_start, work_end)
alexander_free_monday = find_free_slots(alexander_busy["Monday"], work_start, work_end)
alexander_free_tuesday = find_free_slots(alexander_busy["Tuesday"], work_start, work_end)

# Find common free slots
def find_common_slots(slots1, slots2):
    common_slots = []
    i, j = 0, 0
    while i < len(slots1) and j < len(slots2):
        start1, end1 = slots1[i]
        start2, end2 = slots2[j]
        common_start = max(start1, start2)
        common_end = min(end1, end2)
        if common_start < common_end:
            common_slots.append((common_start, common_end))
        if end1 <= end2:
            i += 1
        else:
            j += 1
    return common_slots

common_free_monday = find_common_slots(russell_free_monday, alexander_free_monday)
common_free_tuesday = find_common_slots(russell_free_tuesday, alexander_free_tuesday)

# Apply Russell's preference for Tuesday
common_free_tuesday = [(start, end) for start, end in common_free_tuesday if start >= datetime.strptime("13:30", "%H:%M")]

# Find a suitable time slot with a duration of one hour
def find_suitable_slot(slots):
    for start, end in slots:
        if (end - start) >= timedelta(hours=1):
            return start, start + timedelta(hours=1)
    return None

suitable_slot_monday = find_suitable_slot(common_free_monday)
suitable_slot_tuesday = find_suitable_slot(common_free_tuesday)

# Output the result
if suitable_slot_monday:
    start_time, end_time = suitable_slot_monday
    print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}, Monday")
elif suitable_slot_tuesday:
    start_time, end_time = suitable_slot_tuesday
    print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}, Tuesday")
else:
    print("No suitable time slot found.")