def time_to_minutes(t_str):
    hours, minutes = map(int, t_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Define working hours and meeting duration (in minutes)
working_start = time_to_minutes("09:00")
working_end = time_to_minutes("17:00")
meeting_duration = 30  # in minutes

# Busy intervals for each participant (start, end) in minutes
gregory_busy = [
    (time_to_minutes("09:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:30")),
    (time_to_minutes("12:30"), time_to_minutes("13:00")),
    (time_to_minutes("13:30"), time_to_minutes("14:00"))
]

natalie_busy = []  # Natalie is free all day

christine_busy = [
    (time_to_minutes("09:00"), time_to_minutes("11:30")),
    (time_to_minutes("13:30"), time_to_minutes("17:00"))
]

vincent_busy = [
    (time_to_minutes("09:00"), time_to_minutes("09:30")),
    (time_to_minutes("10:30"), time_to_minutes("12:00")),
    (time_to_minutes("12:30"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("17:00"))
]

def compute_free_intervals(busy_intervals):
    # Start with the full working day and subtract busy slots.
    busy_intervals = sorted(busy_intervals)
    free_intervals = []
    current_start = working_start
    
    for b_start, b_end in busy_intervals:
        if current_start < b_start:
            free_intervals.append((current_start, b_start))
        # Move current_start to the end of this busy period if it's later.
        current_start = max(current_start, b_end)
    
    if current_start < working_end:
        free_intervals.append((current_start, working_end))
    
    return free_intervals

# Calculate free intervals for each participant
gregory_free   = compute_free_intervals(gregory_busy)
natalie_free   = compute_free_intervals(natalie_busy)
christine_free = compute_free_intervals(christine_busy)
vincent_free   = compute_free_intervals(vincent_busy)

def intersect_interval_lists(list1, list2):
    i, j = 0, 0
    intersections = []
    
    while i < len(list1) and j < len(list2):
        start1, end1 = list1[i]
        start2, end2 = list2[j]
        # Find the intersection between the two intervals.
        inter_start = max(start1, start2)
        inter_end   = min(end1, end2)
        
        if inter_end - inter_start >= meeting_duration:
            intersections.append((inter_start, inter_end))
        
        # Move to the next interval in the list that ends earlier.
        if end1 < end2:
            i += 1
        else:
            j += 1
            
    return intersections

# Compute the common free intervals among all participants.
common_free = gregory_free
for free_list in (natalie_free, christine_free, vincent_free):
    common_free = intersect_interval_lists(common_free, free_list)

# Find the earliest meeting slot that can accommodate the meeting duration.
meeting_slot = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_slot = (start, start + meeting_duration)
        break

day = "Monday"
if meeting_slot:
    meeting_start, meeting_end = meeting_slot
    # Output format: HH:MM:HH:MM along with the day.
    meeting_time_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    print(f"{day} {meeting_time_str}")
else:
    print("No available meeting slot found.")