from datetime import datetime, timedelta

def find_meeting_time(christine_busy, helen_busy, meeting_duration, max_helen_end):
    # Define the workday start and end times
    workday_start = datetime.strptime("09:00", "%H:%M")
    workday_end = datetime.strptime("17:00", "%H:%M")
    
    # Convert busy times to datetime objects
    christine_busy_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in christine_busy]
    helen_busy_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in helen_busy]
    
    # Create a list of available slots for Christine
    christine_free_slots = []
    current_time = workday_start
    
    for start, end in sorted(christine_busy_times):
        if current_time < start:
            christine_free_slots.append((current_time, start))
        current_time = max(current_time, end)
    
    if current_time < workday_end:
        christine_free_slots.append((current_time, workday_end))
    
    # Create a list of available slots for Helen
    helen_free_slots = []
    current_time = workday_start
    
    for start, end in sorted(helen_busy_times):
        if current_time < start:
            helen_free_slots.append((current_time, start))
        current_time = max(current_time, end)
    
    if current_time < workday_end:
        helen_free_slots.append((current_time, workday_end))
    
    # Find common free slots
    common_free_slots = []
    for c_start, c_end in christine_free_slots:
        for h_start, h_end in helen_free_slots:
            overlap_start = max(c_start, h_start)
            overlap_end = min(c_end, h_end)
            if overlap_end - overlap_start >= timedelta(minutes=meeting_duration):
                common_free_slots.append((overlap_start, overlap_end))
    
    # Filter slots that end before max_helen_end
    valid_slots = [slot for slot in common_free_slots if slot[1] <= datetime.strptime(max_helen_end, "%H:%M")]
    
    # Output the first valid slot found
    if valid_slots:
        start, end = valid_slots[0]
        return f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')}, Monday"
    else:
        return "No valid meeting time found"

# Define the busy times for Christine and Helen
christine_busy = [("11:00", "11:30"), ("15:00", "15:30")]
helen_busy = [("09:30", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:30", "16:00"), ("16:30", "17:00")]

# Define the meeting duration and Helen's maximum end time
meeting_duration = 30
max_helen_end = "15:00"

# Find and print the meeting time
print(find_meeting_time(christine_busy, helen_busy, meeting_duration, max_helen_end))