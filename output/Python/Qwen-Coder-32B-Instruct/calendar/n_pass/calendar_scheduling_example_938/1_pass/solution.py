from datetime import datetime, timedelta

# Define the work hours and busy times
work_start = 9
work_end = 17
meeting_duration = 0.5  # in hours

# Busy times for Eugene
eugene_busy = {
    'Monday': [(11, 12), (13.5, 14), (14.5, 15), (16, 16.5)],
    'Tuesday': [],
    'Wednesday': [(9, 9.5), (11, 11.5), (12, 12.5), (13.5, 15)],
    'Thursday': [(9.5, 10), (11, 12.5)],
    'Friday': [(10.5, 11), (12, 12.5), (13, 13.5)]
}

# Busy times for Eric
eric_busy = {
    'Monday': [(9, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9, 11.5), (12, 14), (14.5, 16.5)],
    'Thursday': [(9, 17)],
    'Friday': [(9, 11), (11.5, 17)]
}

# Function to check if a time slot is free for both participants
def is_slot_free(day, start, end):
    for busy_start, busy_end in eugene_busy[day]:
        if not (end <= busy_start or start >= busy_end):
            return False
    for busy_start, busy_end in eric_busy[day]:
        if not (end <= busy_start or start >= busy_end):
            return False
    return True

# Find a suitable time slot
for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']:
    if day == 'Wednesday':
        continue  # Eric wants to avoid more meetings on Wednesday
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        if is_slot_free(day, current_time, current_time + meeting_duration):
            start_time_str = f"{int(current_time):02}:{int((current_time % 1) * 60):02}"
            end_time_str = f"{int(current_time + meeting_duration):02}:{int(((current_time + meeting_duration) % 1) * 60):02}"
            print(f"{start_time_str}:{end_time_str} {day}")
            break
        current_time += 0.5