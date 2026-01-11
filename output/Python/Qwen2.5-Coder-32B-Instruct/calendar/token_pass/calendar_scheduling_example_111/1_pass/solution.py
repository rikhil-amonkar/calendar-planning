from datetime import datetime, timedelta

# Define the workday start and end times
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define the busy periods for each participant
busy_periods = {
    "Gregory": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M"))],
    "Natalie": [],
    "Christine": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("13:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Vincent": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

def find_free_slots(busy_times, work_start, work_end):
    current_time = work_start
    free_slots = []
    
    for busy_start, busy_end in sorted(busy_times):
        if current_time < busy_start:
            free_slots.append((current_time, busy_start))
        current_time = max(current_time, busy_end)
    
    if current_time < work_end:
        free_slots.append((current_time, work_end))
    
    return free_slots

def find_common_free_slot(free_slots_list, meeting_duration):
    # Initialize the common free slots with the first person's free slots
    common_free_slots = free_slots_list[0]
    
    # Intersect with each subsequent person's free slots
    for free_slots in free_slots_list[1:]:
        new_common_free_slots = []
        for start1, end1 in common_free_slots:
            for start2, end2 in free_slots:
                overlap_start = max(start1, start2)
                overlap_end = min(end1, end2)
                if overlap_end - overlap_start >= meeting_duration:
                    new_common_free_slots.append((overlap_start, overlap_end))
        common_free_slots = new_common_free_slots
    
    return common_free_slots

# Calculate free slots for each participant
free_slots_list = [find_free_slots(busy_periods[name], work_start, work_end) for name in busy_periods]

# Find a common free slot that fits the meeting duration
meeting_duration = timedelta(minutes=30)
common_free_slots = find_common_free_slot(free_slots_list, meeting_duration)

# Output the first available common free slot
if common_free_slots:
    start_time, end_time = common_free_slots[0]
    print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}:Monday")
else:
    print("No common free slot found.")