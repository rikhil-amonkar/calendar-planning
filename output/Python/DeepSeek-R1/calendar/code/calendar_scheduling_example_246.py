def convert_time(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def find_meeting_time(busy_slots, work_start, work_end, duration):
    for start in range(work_start, work_end - duration + 1, 15):
        end = start + duration
        if all(not any(slot_start <= start < slot_end or slot_start < end <= slot_end for slot_start, slot_end in person) for person in busy_slots.values()):
            return start, end
    return None

participants = {
    'Jacob': ['13:30-14:00', '14:30-15:00'],
    'Diana': ['9:30-10:00', '11:30-12:00', '13:00-13:30', '16:00-16:30'],
    'Adam': ['9:30-10:30', '11:00-12:30', '15:30-16:00'],
    'Angela': ['9:30-10:00', '10:30-12:00', '13:00-15:30', '16:00-16:30'],
    'Dennis': ['9:00-9:30', '10:30-11:30', '13:00-15:00', '16:30-17:00']
}

busy_slots = {}
for person, slots in participants.items():
    busy_slots[person] = []
    for slot in slots:
        start_str, end_str = slot.split('-')
        busy_slots[person].append((convert_time(start_str), convert_time(end_str)))

work_start = convert_time('09:00')
work_end = convert_time('17:00')
duration = 30

result = find_meeting_time(busy_slots, work_start, work_end, duration)

def format_time(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

if result:
    start, end = result
    print(f"Monday:{format_time(start)}:{format_time(end)}")
else:
    print("No suitable time found")