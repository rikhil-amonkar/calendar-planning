def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def find_meeting_slot():
    # Meeting duration in minutes
    duration = 30
    
    # Work hours and constraints
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    evelyn_max = time_to_minutes("13:00")  # Evelyn doesn't want to meet after 13:00
    
    # Randy's busy intervals (converted to minutes)
    randy_busy = [
        (time_to_minutes("9:00"), time_to_minutes("10:30")),
        (time_to_minutes("11:00"), time_to_minutes("15:30")),
        (time_to_minutes("16:00"), time_to_minutes("17:00"))
    ]
    
    # Find Randy's free intervals within work hours
    randy_free = []
    prev_end = work_start
    for start, end in randy_busy:
        if start > prev_end:
            randy_free.append((prev_end, start))
        prev_end = end
    if prev_end < work_end:
        randy_free.append((prev_end, work_end))
    
    # Find slots that fit meeting duration and Evelyn's constraint
    for start, end in randy_free:
        slot_start = start
        slot_end = slot_start + duration
        
        # Check if slot fits within Evelyn's availability (before 13:00) and within free interval
        if slot_end <= evelyn_max and slot_end <= end:
            return "Monday", minutes_to_time(slot_start), minutes_to_time(slot_end)
    
    return None  # Should not happen per problem statement

# Get meeting details
day, start_time, end_time = find_meeting_slot()
print(f"{day} {start_time}:{end_time}")