from datetime import datetime, timedelta

# Function to find the first available meeting time
def find_meeting_time(available_times, meeting_duration):
    for start, end in available_times:
        if (end - start) >= meeting_duration:
            return start, start + meeting_duration
    return None

# Define participants' schedules
andrew_schedule = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
grace_schedule = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
samuel_schedule = [
    (datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
    (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
    (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
    (datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
    (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
]

# Combine schedules to understand availability
def get_available_times(schedules):
    combined_schedule = []
    for schedule in schedules:
        for start, end in schedule:
            combined_schedule.append((start, end))
    
    # Create full day's schedule
    full_day = [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
    
    # Calculate free times
    free_times = []
    for start, end in full_day:
        current_start = start
        for block_start, block_end in sorted(combined_schedule):
            if current_start < block_start:
                free_times.append((current_start, block_start))
                current_start = block_end
            elif current_start < block_end:
                current_start = block_end
        if current_start < end:
            free_times.append((current_start, end))
    
    return free_times

# Meeting duration
meeting_duration = timedelta(minutes=30)

# Get available times for all participants
available_times = get_available_times([andrew_schedule, grace_schedule, samuel_schedule])

# Find meeting time
meeting_start, meeting_end = find_meeting_time(available_times, meeting_duration)

# Output the result
if meeting_start and meeting_end:
    print(f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}")
    print("Monday")