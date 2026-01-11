from datetime import datetime, timedelta

# Define the work hours
start_time = datetime.strptime("09:00", "%H:%M")
end_time = datetime.strptime("17:00", "%H:%M")

# Define busy times for each participant
busy_times = {
    "Anthony": [
        (datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))
    ],
    "Pamela": [
        (datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
        (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ],
    "Zachary": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
        (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
        (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
        (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ]
}

# Function to find free time slots for a participant
def find_free_slots(busy_times, start_time, end_time):
    current_time = start_time
    free_slots = []
    
    for busy_start, busy_end in sorted(busy_times):
        if current_time < busy_start:
            free_slots.append((current_time, busy_start))
        current_time = max(current_time, busy_end)
    
    if current_time < end_time:
        free_slots.append((current_time, end_time))
    
    return free_slots

# Find free slots for each participant
free_slots = {name: find_free_slots(times, start_time, end_time) for name, times in busy_times.items()}

# Function to find overlapping free slots
def find_overlapping_slots(slots_list):
    if not slots_list:
        return []
    
    # Start with the first person's slots
    overlapping_slots = slots_list[0]
    
    for slots in slots_list[1:]:
        new_overlapping_slots = []
        for start1, end1 in overlapping_slots:
            for start2, end2 in slots:
                overlap_start = max(start1, start2)
                overlap_end = min(end1, end2)
                if overlap_start < overlap_end:
                    new_overlapping_slots.append((overlap_start, overlap_end))
        overlapping_slots = new_overlapping_slots
    
    return overlapping_slots

# Find overlapping free slots for all participants
all_free_slots = [free_slots[name] for name in free_slots]
overlapping_slots = find_overlapping_slots(all_free_slots)

# Apply Pamela's constraint (not after 14:30)
pamela_constraint = datetime.strptime("14:30", "%H:%M")
filtered_slots = [(start, end) for start, end in overlapping_slots if start < pamela_constraint]

# Find a slot that fits the meeting duration (1 hour)
meeting_duration = timedelta(hours=1)
suitable_slot = next((slot for slot in filtered_slots if slot[1] - slot[0] >= meeting_duration), None)

# Output the result
if suitable_slot:
    start, end = suitable_slot
    print(f"Monday {start.strftime('%H:%M')}:{end.strftime('%H:%M')}")
else:
    print("No suitable time slot found.")