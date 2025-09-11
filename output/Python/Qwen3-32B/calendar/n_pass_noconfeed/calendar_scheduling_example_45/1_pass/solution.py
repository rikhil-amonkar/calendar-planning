def min_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

samuel_blocked = [
    (9*60, 10*60 + 30),  # 9:00-10:30
    (11*60 + 30, 12*60), # 11:30-12:00
    (13*60, 13*60 + 30), # 13:00-13:30
    (14*60, 16*60),      # 14:00-16:00
    (16*60 + 30, 17*60)  # 16:30-17:00
]

workday_start = 9 * 60
workday_end = 17 * 60
required_duration = 30

available_slots = []
prev_end = workday_start

sorted_blocked = sorted(samuel_blocked, key=lambda x: x[0])

for start, end in sorted_blocked:
    if prev_end < start:
        available_slots.append((prev_end, start))
    prev_end = end

if prev_end < workday_end:
    available_slots.append((prev_end, workday_end))

earliest_start = None
earliest_end = None

for slot_start, slot_end in available_slots:
    if slot_end - slot_start >= required_duration:
        earliest_start = slot_start
        earliest_end = earliest_start + required_duration
        break

start_time = min_to_time(earliest_start)
end_time = min_to_time(earliest_end)
day = "Monday"

print(f"{start_time}:{end_time} {day}")