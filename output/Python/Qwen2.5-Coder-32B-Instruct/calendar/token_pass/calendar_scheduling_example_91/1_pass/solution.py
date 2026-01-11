def time_to_minutes(time_str):
    """Converts time in 'HH:MM' format to minutes since start of the day."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Converts minutes since start of the day to 'HH:MM' format."""
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

def find_free_slots(busy_times, start, end):
    """Finds free slots in the given time range excluding busy times."""
    free_slots = []
    current_start = start
    
    for busy_start, busy_end in sorted(busy_times):
        if current_start < busy_start:
            free_slots.append((current_start, busy_start))
        current_start = max(current_start, busy_end)
    
    if current_start < end:
        free_slots.append((current_start, end))
    
    return free_slots

def find_common_free_slot(free_slots_list, meeting_duration):
    """Finds a common free slot that fits the meeting duration."""
    if not free_slots_list:
        return None
    
    # Initialize with the first person's free slots
    common_free_slots = free_slots_list[0]
    
    for person_free_slots in free_slots_list[1:]:
        new_common_free_slots = []
        for start1, end1 in common_free_slots:
            for start2, end2 in person_free_slots:
                overlap_start = max(start1, start2)
                overlap_end = min(end1, end2)
                if overlap_end - overlap_start >= meeting_duration:
                    new_common_free_slots.append((overlap_start, overlap_end))
        common_free_slots = new_common_free_slots
    
    if common_free_slots:
        return common_free_slots[0]
    return None

# Define work hours in minutes
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Define busy times for each participant
danielle_busy = [(time_to_minutes("09:00"), time_to_minutes("10:00")),
                 (time_to_minutes("10:30"), time_to_minutes("11:00")),
                 (time_to_minutes("14:30"), time_to_minutes("15:00")),
                 (time_to_minutes("15:30"), time_to_minutes("16:00")),
                 (time_to_minutes("16:30"), time_to_minutes("17:00"))]

bruce_busy = [(time_to_minutes("11:00"), time_to_minutes("11:30")),
              (time_to_minutes("12:30"), time_to_minutes("13:00")),
              (time_to_minutes("14:00"), time_to_minutes("14:30")),
              (time_to_minutes("15:30"), time_to_minutes("16:00"))]

eric_busy = [(time_to_minutes("09:00"), time_to_minutes("09:30")),
             (time_to_minutes("10:00"), time_to_minutes("11:00")),
             (time_to_minutes("11:30"), time_to_minutes("13:00")),
             (time_to_minutes("14:30"), time_to_minutes("15:30"))]

# Find free slots for each participant
danielle_free = find_free_slots(danielle_busy, work_start, work_end)
bruce_free = find_free_slots(bruce_busy, work_start, work_end)
eric_free = find_free_slots(eric_busy, work_start, work_end)

# Find a common free slot that fits the meeting duration
meeting_duration = 60  # 1 hour
common_slot = find_common_free_slot([danielle_free, bruce_free, eric_free], meeting_duration)

if common_slot:
    start_time = minutes_to_time(common_slot[0])
    end_time = minutes_to_time(common_slot[1])
    print(f"Meeting time: {start_time}:{end_time} on Monday")
else:
    print("No common free slot found.")