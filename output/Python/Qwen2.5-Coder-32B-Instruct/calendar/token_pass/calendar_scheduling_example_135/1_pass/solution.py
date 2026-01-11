from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def get_available_slots(busy_times, start, end, duration):
    current = start
    available_slots = []
    for busy_start, busy_end in busy_times:
        if current < busy_start:
            if busy_start - current >= duration:
                available_slots.append((current, busy_start))
        current = max(current, busy_end)
    if end - current >= duration:
        available_slots.append((current, end))
    return available_slots

def find_common_availability(slots_list, duration):
    if not slots_list:
        return None
    
    common_slots = slots_list[0]
    for slots in slots_list[1:]:
        new_common_slots = []
        for start1, end1 in common_slots:
            for start2, end2 in slots:
                overlap_start = max(start1, start2)
                overlap_end = min(end1, end2)
                if overlap_end - overlap_start >= duration:
                    new_common_slots.append((overlap_start, overlap_end))
        common_slots = new_common_slots
        if not common_slots:
            return None
    return common_slots

def format_time(slot):
    start, end = slot
    return f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')}"

# Define the start and end of the workday
work_start = parse_time("09:00")
work_end = parse_time("17:00")
meeting_duration = timedelta(hours=0, minutes=30)

# Define the busy times for each participant
busy_times = {
    "Eric": [],
    "Ashley": [(parse_time("10:00"), parse_time("10:30")), 
               (parse_time("11:00"), parse_time("12:00")), 
               (parse_time("12:30"), parse_time("13:00")), 
               (parse_time("15:00"), parse_time("16:00"))],
    "Ronald": [(parse_time("09:00"), parse_time("09:30")), 
               (parse_time("10:00"), parse_time("11:30")), 
               (parse_time("12:30"), parse_time("14:00")), 
               (parse_time("14:30"), parse_time("17:00"))],
    "Larry": [(parse_time("09:00"), parse_time("12:00")), 
              (parse_time("13:00"), parse_time("17:00"))]
}

# Get available slots for each participant
available_slots = [get_available_slots(busy_times[name], work_start, work_end, meeting_duration) for name in busy_times]

# Find common availability
common_availability = find_common_availability(available_slots, meeting_duration)

# Output the solution
if common_availability:
    print(f"Monday, {format_time(common_availability[0])}")
else:
    print("No common availability found.")