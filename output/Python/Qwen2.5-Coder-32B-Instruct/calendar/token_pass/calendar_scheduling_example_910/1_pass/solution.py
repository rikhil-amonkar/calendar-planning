# Define the work hours and meeting duration
work_start = 9
work_end = 17
meeting_duration = 1

# Define the busy times for each participant
bryan_busy_times = {
    'Monday': [],
    'Tuesday': [],
    'Wednesday': [],
    'Thursday': [(9.5, 10.0), (12.5, 13.0)],
    'Friday': [(10.5, 11.0), (14.0, 14.5)]
}

nicholas_busy_times = {
    'Monday': [(11.5, 12.0), (13.0, 15.5)],
    'Tuesday': [(9.0, 9.5), (11.0, 13.5), (14.0, 16.5)],
    'Wednesday': [(9.0, 9.5), (10.0, 11.0), (11.5, 13.5), (14.0, 14.5), (15.0, 16.5)],
    'Thursday': [(10.5, 11.5), (12.0, 12.5), (15.0, 15.5), (16.5, 17.0)],
    'Friday': [(9.0, 10.0), (11.0, 12.0), (12.5, 14.5), (15.5, 16.0), (16.5, 17.0)]
}

# Constraints
bryan_avoid_tuesday = True
nicholas_avoid_monday_thursday = True

# Function to check if a time slot is free for both participants
def is_slot_free(day, start_time, end_time, bryan_busy, nicholas_busy):
    for busy_start, busy_end in bryan_busy.get(day, []):
        if not (end_time <= busy_start or start_time >= busy_end):
            return False
    for busy_start, busy_end in nicholas_busy.get(day, []):
        if not (end_time <= busy_start or start_time >= busy_end):
            return False
    return True

# Find a suitable meeting time
for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']:
    if (day == 'Tuesday' and bryan_avoid_tuesday) or (day in ['Monday', 'Thursday'] and nicholas_avoid_monday_thursday):
        continue
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        if is_slot_free(day, current_time, current_time + meeting_duration, bryan_busy_times, nicholas_busy_times):
            meeting_start = f"{int(current_time):02}:{int((current_time % 1) * 60):02}"
            meeting_end = f"{int(current_time + meeting_duration):02}:{int(((current_time + meeting_duration) % 1) * 60):02}"
            print(f"Meeting time: {meeting_start}:{meeting_end} on {day}")
            break
        current_time += 0.5
    else:
        continue
    break