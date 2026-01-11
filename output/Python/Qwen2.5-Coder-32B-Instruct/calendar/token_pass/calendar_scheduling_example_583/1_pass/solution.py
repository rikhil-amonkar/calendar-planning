from datetime import datetime, timedelta

# Define the workday start and end times
workday_start = datetime.strptime("09:00", "%H:%M")
workday_end = datetime.strptime("17:00", "%H:%M")

# Busy times for Lisa and Anthony
lisa_busy_times = [
    ("09:00", "09:30"),
    ("10:30", "11:00"),
    ("14:00", "16:00")
]

anthony_busy_times = [
    ("09:00", "09:30"),
    ("11:00", "11:30"),
    ("12:30", "13:30"),
    ("14:00", "15:00"),
    ("15:30", "16:00"),
    ("16:30", "17:00")
]

# Convert busy times to datetime objects
def convert_to_datetime(busy_times):
    return [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in busy_times]

lisa_busy_times = convert_to_datetime(lisa_busy_times)
anthony_busy_times = convert_to_datetime(anthony_busy_times)

# Function to get free times
def get_free_times(busy_times, start=workday_start, end=workday_end):
    free_times = []
    current_time = start
    for busy_start, busy_end in busy_times:
        if current_time < busy_start:
            free_times.append((current_time, busy_start))
        current_time = max(current_time, busy_end)
    if current_time < end:
        free_times.append((current_time, end))
    return free_times

lisa_free_times = get_free_times(lisa_busy_times)
anthony_free_times = get_free_times(anthony_busy_times)

# Find common free times
def find_common_free_times(free_times_1, free_times_2):
    common_free_times = []
    i, j = 0, 0
    while i < len(free_times_1) and j < len(free_times_2):
        start_1, end_1 = free_times_1[i]
        start_2, end_2 = free_times_2[j]
        
        # Find the overlap
        overlap_start = max(start_1, start_2)
        overlap_end = min(end_1, end_2)
        
        if overlap_start < overlap_end:
            common_free_times.append((overlap_start, overlap_end))
        
        # Move to the next interval
        if end_1 <= end_2:
            i += 1
        else:
            j += 1
    return common_free_times

common_free_times = find_common_free_times(lisa_free_times, anthony_free_times)

# Find the first common free time slot that fits the meeting duration
meeting_duration = timedelta(minutes=30)
for start, end in common_free_times:
    if end - start >= meeting_duration:
        meeting_start = start.strftime("%H:%M")
        meeting_end = (start + meeting_duration).strftime("%H:%M")
        break

# Output the result
print(f"{meeting_start}:{meeting_end} Monday")