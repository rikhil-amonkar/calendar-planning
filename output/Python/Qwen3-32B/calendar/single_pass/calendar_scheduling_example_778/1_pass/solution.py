def time_str_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def get_available_slots(work_start, work_end, busy_slots):
    busy_slots_sorted = sorted(busy_slots, key=lambda x: x[0])
    available = []
    current_start = work_start
    for start, end in busy_slots_sorted:
        if current_start < start:
            available.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        available.append((current_start, work_end))
    return available

def find_overlapping_slots(slots1, slots2, meeting_duration):
    for s1_start, s1_end in slots1:
        for s2_start, s2_end in slots2:
            overlap_start = max(s1_start, s2_start)
            overlap_end = min(s1_end, s2_end)
            if overlap_start < overlap_end:
                if overlap_end - overlap_start >= meeting_duration:
                    return (overlap_start, overlap_end)
    return None

susan_schedule = {
    'Monday': [('12:30', '13:00'), ('13:30', '14:00')],
    'Tuesday': [('11:30', '12:00')],
    'Wednesday': [('9:30', '10:30'), ('14:00', '14:30'), ('15:30', '16:30')],
}

sandra_schedule = {
    'Monday': [('9:00', '13:00'), ('14:00', '15:00'), ('16:00', '16:30')],
    'Tuesday': [('9:00', '9:30'), ('10:30', '12:00'), ('12:30', '13:30'), ('14:00', '14:30'), ('16:00', '17:00')],
    'Wednesday': [('9:00', '11:30'), ('12:00', '12:30'), ('13:00', '17:00')],
}

valid_slots = []

for day in ['Monday', 'Tuesday', 'Wednesday']:
    # Susan's available slots
    susan_busy = susan_schedule.get(day, [])
    susan_busy_minutes = [ (time_str_to_minutes(s), time_str_to_minutes(e)) for s, e in susan_busy ]
    susan_work_start = 540  # 9:00 AM
    susan_work_end = 1020   # 5:00 PM
    susan_available = get_available_slots(susan_work_start, susan_work_end, susan_busy_minutes)
    
    # Sandra's available slots
    sandra_busy = sandra_schedule.get(day, [])
    sandra_busy_minutes = [ (time_str_to_minutes(s), time_str_to_minutes(e)) for s, e in sandra_busy ]
    if day == 'Monday':
        sandra_work_end = 960  # 4:00 PM
    else:
        sandra_work_end = 1020  # 5:00 PM
    sandra_work_start = 540  # 9:00 AM
    sandra_available = get_available_slots(sandra_work_start, sandra_work_end, sandra_busy_minutes)
    
    # Find overlapping slot
    overlapping_slot = find_overlapping_slots(susan_available, sandra_available, 30)
    if overlapping_slot:
        valid_slots.append((day, overlapping_slot))

# Find the earliest valid slot that is not on Tuesday
earliest_non_tuesday = None
for day, slot in valid_slots:
    if day == 'Tuesday':
        continue
    if earliest_non_tuesday is None or slot[0] < earliest_non_tuesday[1][0]:
        earliest_non_tuesday = (day, slot)

if earliest_non_tuesday:
    day, slot = earliest_non_tuesday
else:
    # Pick earliest on Tuesday
    day, slot = min(valid_slots, key=lambda x: x[1][0])

start_min, end_min = slot
start_time = f"{start_min//60:02d}:{start_min%60:02d}"
end_time = f"{end_min//60:02d}:{end_min%60:02d}"
print(f"{day} {start_time}:{end_time}")