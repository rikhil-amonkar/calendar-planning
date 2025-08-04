from datetime import datetime, timedelta

# Define the work hours and breaks for Nicole and Ruth
nicole_schedule = {
    'Monday': [(9, 9.5), (13, 13.5), (14.5, 15.5)],
    'Tuesday': [(9, 9.5), (11.5, 13.5), (14.5, 15.5)],
    'Wednesday': [(10, 11), (12.5, 15), (16, 17)]
}

ruth_schedule = {
    'Monday': [(9, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9, 10.5), (11, 11.5), (12, 12.5), (13.5, 15.5), (16, 16.5)]
}

# Meeting duration in hours
meeting_duration = 0.5

# Function to find free slots
def find_free_slots(schedule, start_hour=9, end_hour=17):
    free_slots = []
    for day, blocks in schedule.items():
        current_start = start_hour
        for block_start, block_end in blocks:
            if current_start < block_start:
                free_slots.append((day, current_start, block_start))
            current_start = max(current_start, block_end)
        if current_start < end_hour:
            free_slots.append((day, current_start, end_hour))
    return free_slots

# Function to find common free slots
def find_common_slots(nicole_free, ruth_free):
    common_slots = []
    i, j = 0, 0
    while i < len(nicole_free) and j < len(ruth_free):
        n_day, n_start, n_end = nicole_free[i]
        r_day, r_start, r_end = ruth_free[j]
        
        if n_day == r_day:
            overlap_start = max(n_start, r_start)
            overlap_end = min(n_end, r_end)
            if overlap_end - overlap_start >= meeting_duration:
                common_slots.append((n_day, overlap_start, overlap_start + meeting_duration))
            if n_end <= r_end:
                i += 1
            else:
                j += 1
        elif n_day < r_day:
            i += 1
        else:
            j += 1
    return common_slots

# Find free slots for Nicole and Ruth
nicole_free_slots = find_free_slots(nicole_schedule)
ruth_free_slots = find_free_slots(ruth_schedule)

# Find common free slots
common_free_slots = find_common_slots(nicole_free_slots, ruth_free_slots)

# Filter out slots after 13:30 on Wednesday
filtered_slots = [slot for slot in common_free_slots if not (slot[0] == 'Wednesday' and slot[1] > 13.5)]

# Output the first available slot
if filtered_slots:
    day, start, end = filtered_slots[0]
    start_time = f"{int(start):02}:{int((start % 1) * 60):02}"
    end_time = f"{int(end):02}:{int((end % 1) * 60):02}"
    print(f"{start_time}:{end_time} {day}")
else:
    print("No available slots found.")