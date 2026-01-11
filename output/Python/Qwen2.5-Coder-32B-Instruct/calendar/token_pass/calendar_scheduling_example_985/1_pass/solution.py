# Define the busy times for Diane and Matthew
diane_busy = {
    'Monday': [(12, 12.5), (15, 15.5)],
    'Tuesday': [(10, 11), (11.5, 12), (12.5, 13), (16, 17)],
    'Wednesday': [(9, 9.5), (14.5, 15), (16.5, 17)],
    'Thursday': [(15.5, 16.5)],
    'Friday': [(9.5, 11.5), (14.5, 15), (16, 17)]
}

matthew_busy = {
    'Monday': [(9, 10), (10.5, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9, 11), (12, 14.5), (16, 17)],
    'Thursday': [(9, 16)],
    'Friday': [(9, 17)]
}

# Define the work hours and meeting duration
work_hours = (9, 17)
meeting_duration = 1

# Function to find free slots in a day
def find_free_slots(busy_times, work_hours):
    start, end = work_hours
    free_slots = []
    current_time = start
    
    for busy_start, busy_end in sorted(busy_times):
        if current_time < busy_start:
            free_slots.append((current_time, busy_start))
        current_time = max(current_time, busy_end)
    
    if current_time < end:
        free_slots.append((current_time, end))
    
    return free_slots

# Function to filter slots based on duration
def filter_slots_by_duration(slots, duration):
    return [slot for slot in slots if slot[1] - slot[0] >= duration]

# Find suitable meeting slots
suitable_slot = None

for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']:
    diane_free = find_free_slots(diane_busy.get(day, []), work_hours)
    matthew_free = find_free_slots(matthew_busy.get(day, []), work_hours)
    
    # Find common free slots
    common_free = []
    i, j = 0, 0
    while i < len(diane_free) and j < len(matthew_free):
        start_d, end_d = diane_free[i]
        start_m, end_m = matthew_free[j]
        
        start_common = max(start_d, start_m)
        end_common = min(end_d, end_m)
        
        if start_common < end_common:
            common_free.append((start_common, end_common))
        
        if end_d < end_m:
            i += 1
        else:
            j += 1
    
    # Filter slots based on meeting duration
    filtered_slots = filter_slots_by_duration(common_free, meeting_duration)
    
    # Apply Matthew's preference for Wednesday
    if day == 'Wednesday':
        filtered_slots = [(s, e) for s, e in filtered_slots if s >= 12.5]
    
    # Check if there is a suitable slot
    if filtered_slots:
        suitable_slot = (day, filtered_slots[0])
        break

# Output the result
if suitable_slot:
    day, (start, end) = suitable_slot
    start_time = f"{int(start):02}:{int((start % 1) * 60):02}"
    end_time = f"{int(end):02}:{int((end % 1) * 60):02}"
    print(f"{start_time}:{end_time} {day}")
else:
    print("No suitable time found.")