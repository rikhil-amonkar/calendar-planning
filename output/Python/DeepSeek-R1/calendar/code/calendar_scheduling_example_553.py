def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define work hours and meeting duration
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30

# Define busy intervals in minutes
eric_busy = [
    (time_to_minutes("12:00"), time_to_minutes("13:00")),
    (time_to_minutes("14:00"), time_to_minutes("15:00"))
]

henry_busy = [
    (time_to_minutes("09:30"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Combine and sort all busy intervals
combined_busy = sorted(eric_busy + henry_busy, key=lambda x: x[0])

# Merge overlapping intervals
merged_busy = []
for start, end in combined_busy:
    if not merged_busy:
        merged_busy.append([start, end])
    else:
        last_start, last_end = merged_busy[-1]
        if start <= last_end:
            merged_busy[-1][1] = max(last_end, end)
        else:
            merged_busy.append([start, end])

# Find free slots considering work hours
free_slots = []
previous_end = work_start
for start, end in merged_busy:
    if start > previous_end:
        free_slots.append((previous_end, start))
    previous_end = max(previous_end, end)
if previous_end < work_end:
    free_slots.append((previous_end, work_end))

# Find first suitable slot considering Henry's preference (prefer before 10:00)
suitable_slot = None
for slot in free_slots:
    slot_start, slot_end = slot
    if slot_end - slot_start >= meeting_duration:
        # Check if slot is before 10:00 first
        if slot_end <= time_to_minutes("10:00"):
            suitable_slot = (slot_start, slot_start + meeting_duration)
            break
if not suitable_slot:  # If no early slot found, take first available
    for slot in free_slots:
        slot_start, slot_end = slot
        if slot_end - slot_start >= meeting_duration:
            suitable_slot = (slot_start, slot_start + meeting_duration)
            break

# Format output
start_time = minutes_to_time(suitable_slot[0])
end_time = minutes_to_time(suitable_slot[1])
print(f"Monday {start_time}:{end_time}")