def find_meeting_time(participants_schedules, duration_minutes, work_start, work_end):
    # Convert time strings to minutes since start of day
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    # Initialize the free slots for the day
    free_slots = []
    current_start = work_start_min
    
    # Collect all busy intervals
    busy_intervals = []
    for person in participants_schedules:
        for busy in person:
            start = time_to_minutes(busy[0])
            end = time_to_minutes(busy[1])
            busy_intervals.append((start, end))
    
    # Sort busy intervals by start time
    busy_intervals.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged_busy = []
    for start, end in busy_intervals:
        if not merged_busy:
            merged_busy.append([start, end])
        else:
            last_start, last_end = merged_busy[-1]
            if start <= last_end:
                # Overlapping or adjacent, merge them
                merged_busy[-1][1] = max(last_end, end)
            else:
                merged_busy.append([start, end])
    
    # Find free slots between merged busy intervals
    for busy_start, busy_end in merged_busy:
        if current_start < busy_start:
            free_slots.append((current_start, busy_start))
        current_start = max(current_start, busy_end)
    
    # Check the slot after the last busy interval
    if current_start < work_end_min:
        free_slots.append((current_start, work_end_min))
    
    # Find the first free slot that can accommodate the meeting
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= duration_minutes:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_minutes
            return (meeting_start, meeting_end)
    
    return None

def minutes_to_time(minutes):
    hh = minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

# Define participants' schedules
participants_schedules = [
    [],  # Eric has no meetings
    [("10:00", "10:30"), ("11:00", "12:00"), ("12:30", "13:00"), ("15:00", "16:00")],  # Ashley
    [("09:00", "09:30"), ("10:00", "11:30"), ("12:30", "14:00"), ("14:30", "17:00")],  # Ronald
    [("09:00", "12:00"), ("13:00", "17:00")],  # Larry
]

# Meeting parameters
duration_minutes = 30
work_start = "09:00"
work_end = "17:00"
day = "Monday"

# Find meeting time
meeting_time = find_meeting_time(participants_schedules, duration_minutes, work_start, work_end)

if meeting_time:
    start, end = meeting_time
    start_time = minutes_to_time(start)
    end_time = minutes_to_time(end)
    print(f"{day}: {start_time}:{end_time}")
else:
    print("No suitable time found.")