from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def get_free_slots(busy_times, start_time, end_time):
    current = start_time
    free_slots = []
    
    for start, end in busy_times:
        if current < start:
            free_slots.append((current, start))
        current = max(current, end)
    
    if current < end_time:
        free_slots.append((current, end_time))
    
    return free_slots

def find_common_free_slot(free_slots_list, meeting_duration):
    if not free_slots_list:
        return None
    
    common_free_slots = free_slots_list[0]
    
    for free_slots in free_slots_list[1:]:
        new_common_free_slots = []
        for start1, end1 in common_free_slots:
            for start2, end2 in free_slots:
                overlap_start = max(start1, start2)
                overlap_end = min(end1, end2)
                if overlap_end - overlap_start >= meeting_duration:
                    new_common_free_slots.append((overlap_start, overlap_end))
        common_free_slots = new_common_free_slots
        
        if not common_free_slots:
            return None
    
    return common_free_slots[0] if common_free_slots else None

# Define the workday
work_start = parse_time("09:00")
work_end = parse_time("17:00")

# Define the busy times for each participant
busy_times = {
    "Olivia": [(parse_time("12:30"), parse_time("13:30")), (parse_time("14:30"), parse_time("15:00")), (parse_time("16:30"), parse_time("17:00"))],
    "Anna": [],
    "Virginia": [(parse_time("09:00"), parse_time("10:00")), (parse_time("11:30"), parse_time("16:00")), (parse_time("16:30"), parse_time("17:00"))],
    "Paul": [(parse_time("09:00"), parse_time("09:30")), (parse_time("11:00"), parse_time("11:30")), (parse_time("13:00"), parse_time("14:00")), (parse_time("14:30"), parse_time("16:00")), (parse_time("16:30"), parse_time("17:00"))]
}

# Get free slots for each participant
free_slots_list = [get_free_slots(sorted(busy_times[name]), work_start, work_end) for name in busy_times]

# Find a common free slot
meeting_duration = timedelta(hours=1)
common_free_slot = find_common_free_slot(free_slots_list, meeting_duration)

# Output the result
if common_free_slot:
    start_time, end_time = common_free_slot
    print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}, Monday")
else:
    print("No common free slot found")