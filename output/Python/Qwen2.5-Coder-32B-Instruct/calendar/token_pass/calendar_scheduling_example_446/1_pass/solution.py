from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def get_free_slots(busy_times, start="09:00", end="17:00"):
    start_time = parse_time(start)
    end_time = parse_time(end)
    busy_intervals = sorted([(parse_time(start), parse_time(end)) for start, end in busy_times])
    
    free_slots = []
    current_time = start_time
    
    for busy_start, busy_end in busy_intervals:
        if current_time < busy_start:
            free_slots.append((current_time, busy_start))
        current_time = max(current_time, busy_end)
    
    if current_time < end_time:
        free_slots.append((current_time, end_time))
    
    return free_slots

def find_common_free_slot(free_slots_list):
    if not free_slots_list:
        return None
    
    common_free_slots = free_slots_list[0]
    
    for free_slots in free_slots_list[1:]:
        new_common_slots = []
        i, j = 0, 0
        
        while i < len(common_free_slots) and j < len(free_slots):
            start1, end1 = common_free_slots[i]
            start2, end2 = free_slots[j]
            
            overlap_start = max(start1, start2)
            overlap_end = min(end1, end2)
            
            if overlap_start < overlap_end:
                new_common_slots.append((overlap_start, overlap_end))
            
            if end1 <= end2:
                i += 1
            else:
                j += 1
        
        common_free_slots = new_common_slots
    
    return common_free_slots

def find_meeting_time(participants, duration=30):
    day_of_week = "Monday"
    free_slots_list = []
    
    for name, busy_times in participants.items():
        free_slots = get_free_slots(busy_times)
        free_slots_list.append(free_slots)
    
    common_free_slots = find_common_free_slot(free_slots_list)
    
    for start, end in common_free_slots:
        if (end - start).seconds >= duration * 60:
            meeting_start = start.strftime("%H:%M")
            meeting_end = (start + timedelta(minutes=duration)).strftime("%H:%M")
            return f"{meeting_start}:{meeting_end} {day_of_week}"
    
    return None

participants = {
    "Megan": [("09:00", "09:30"), ("10:00", "11:00"), ("12:00", "12:30")],
    "Christine": [("09:00", "09:30"), ("11:30", "12:00"), ("13:00", "14:00"), ("15:30", "16:30")],
    "Gabriel": [],
    "Sara": [("11:30", "12:00"), ("14:30", "15:00")],
    "Bruce": [("09:30", "10:00"), ("10:30", "12:00"), ("12:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:30")],
    "Kathryn": [("10:00", "15:30"), ("16:00", "16:30")],
    "Billy": [("09:00", "09:30"), ("11:00", "11:30"), ("12:00", "14:00"), ("14:30", "15:30")]
}

meeting_time = find_meeting_time(participants)
print(meeting_time)