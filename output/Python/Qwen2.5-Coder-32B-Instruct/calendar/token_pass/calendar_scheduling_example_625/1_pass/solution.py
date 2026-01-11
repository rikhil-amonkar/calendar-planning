# Define the work hours and constraints
work_hours_start = 9 * 60  # 9:00 AM in minutes from midnight
work_hours_end = 17 * 60   # 5:00 PM in minutes from midnight
meeting_duration = 30      # Meeting duration in minutes

# Define Harold's unavailable times on Monday and Tuesday
harold_unavailable_monday = [(9 * 60, 10 * 60), (10 * 60 + 30, 17 * 60)]
harold_unavailable_tuesday = [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 11 * 60 + 30),
                              (12 * 60 + 30, 13 * 60 + 30), (14 * 60 + 30, 15 * 60 + 30),
                              (16 * 60, 17 * 60)]

# Function to find free slots
def find_free_slots(unavailable_times, start, end, duration):
    current_time = start
    free_slots = []
    for start_unavailable, end_unavailable in unavailable_times:
        if current_time < start_unavailable:
            if start_unavailable - current_time >= duration:
                free_slots.append((current_time, current_time + duration))
        current_time = max(current_time, end_unavailable)
    if current_time < end:
        if end - current_time >= duration:
            free_slots.append((current_time, end))
    return free_slots

# Find free slots on Tuesday
free_slots_tuesday = find_free_slots(harold_unavailable_tuesday, work_hours_start, work_hours_end, meeting_duration)

# Filter slots based on Harold's preference
preferred_slot = None
for start, end in free_slots_tuesday:
    if start >= 14 * 60 + 30:  # 14:30 in minutes from midnight
        preferred_slot = (start, end)
        break

# Output the result
if preferred_slot:
    start_hour, start_minute = divmod(preferred_slot[0], 60)
    end_hour, end_minute = divmod(preferred_slot[1], 60)
    print(f"{start_hour:02}:{start_minute:02}:{end_hour:02}:{end_minute:02} Tuesday")
else:
    print("No suitable time found.")