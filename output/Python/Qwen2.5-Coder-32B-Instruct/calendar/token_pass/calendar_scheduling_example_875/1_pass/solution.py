# Define work hours and meeting duration
work_hours = (9, 17)
meeting_duration = 1

# Define busy times for each participant
natalie_busy = {
    'Monday': [(9, 9.5), (10, 12), (12.5, 13), (14, 14.5), (15, 16.5)],
    'Tuesday': [(9, 9.5), (10, 10.5), (12.5, 14), (16, 17)],
    'Wednesday': [(11, 11.5), (16, 16.5)],
    'Thursday': [(10, 11), (11.5, 15), (15.5, 16), (16.5, 17)]
}

william_busy = {
    'Monday': [(9.5, 11), (11.5, 17)],
    'Tuesday': [(9, 13), (13.5, 16)],
    'Wednesday': [(9, 12.5), (13, 14.5), (15.5, 16), (16.5, 17)],
    'Thursday': [(9, 10.5), (11, 11.5), (12, 12.5), (13, 14), (15, 17)]
}

def find_free_slots(busy_times, start, end):
    """Find free slots in a given busy schedule."""
    current_time = start
    free_slots = []
    for busy_start, busy_end in busy_times:
        if current_time < busy_start:
            free_slots.append((current_time, busy_start))
        current_time = max(current_time, busy_end)
    if current_time < end:
        free_slots.append((current_time, end))
    return free_slots

def find_common_free_slot(natalie_free, william_free):
    """Find common free slots between two people."""
    i, j = 0, 0
    common_slots = []
    while i < len(natalie_free) and j < len(william_free):
        # Calculate the overlap between slots
        start = max(natalie_free[i][0], william_free[j][0])
        end = min(natalie_free[i][1], william_free[j][1])
        if start < end:
            common_slots.append((start, end))
        # Move to the next slot
        if natalie_free[i][1] < william_free[j][1]:
            i += 1
        else:
            j += 1
    return common_slots

# Check each day for a suitable meeting time
for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday']:
    natalie_free = find_free_slots(natalie_busy[day], work_hours[0], work_hours[1])
    william_free = find_free_slots(william_busy[day], work_hours[0], work_hours[1])
    common_slots = find_common_free_slot(natalie_free, william_free)
    
    for start, end in common_slots:
        if end - start >= meeting_duration:
            # Convert float hours to HH:MM format
            start_time = f"{int(start):02}:{int((start % 1) * 60):02}"
            end_time = f"{int(end):02}:{int((end % 1) * 60):02}"
            print(f"Meeting can be scheduled from {start_time}:{end_time} on {day}")
            break
    else:
        continue
    break