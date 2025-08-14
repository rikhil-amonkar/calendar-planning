eric_available = [
    (9 * 60, 12 * 60),   # 9:00-12:00
    (13 * 60, 14 * 60),  # 13:00-14:00
    (15 * 60, 17 * 60),  # 15:00-17:00
]

henry_available = [
    (9 * 60, 9 * 60 + 30),   # 9:00-9:30
    (10 * 60, 10 * 60 + 30), # 10:00-10:30
    (11 * 60, 11 * 60 + 30), # 11:00-11:30
    (12 * 60 + 30, 13 * 60), # 12:30-13:00
    (13 * 60 + 30, 14 * 60 + 30), # 13:30-14:30
    (15 * 60, 16 * 60),      # 15:00-16:00
]

possible_slots = []

for e_start, e_end in eric_available:
    for h_start, h_end in henry_available:
        start = max(e_start, h_start)
        end = min(e_end, h_end)
        if start < end:
            duration = end - start
            if duration >= 30:
                possible_slots.append((start, end))

possible_slots.sort()

selected_slot = None
for slot in possible_slots:
    if slot[1] <= 10 * 60:
        selected_slot = slot
        break
if selected_slot is None:
    selected_slot = possible_slots[0]

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

start_str = minutes_to_time_str(selected_slot[0])
end_str = minutes_to_time_str(selected_slot[1])
day = "Monday"

print(f"{start_str}:{end_str}:{day}")