def time_to_minutes(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

participants = [
    {  # Christine
        "busy": ["9:30-10:30", "12:00-12:30", "13:00-13:30", "14:30-15:00", "16:00-16:30"]
    },
    {  # Janice
        "busy": []
    },
    {  # Bobby
        "busy": ["12:00-12:30", "14:30-15:00"]
    },
    {  # Elizabeth
        "busy": ["9:00-9:30", "11:30-13:00", "13:30-14:00", "15:00-15:30", "16:00-17:00"]
    },
    {  # Tyler
        "busy": ["9:00-11:00", "12:00-12:30", "13:00-13:30", "15:30-16:00", "16:30-17:00"]
    },
    {  # Edward
        "busy": ["9:00-9:30", "10:00-11:00", "11:30-14:00", "14:30-15:30", "16:00-17:00"]
    }
]

busy_intervals = []
for person in participants:
    for interval in person["busy"]:
        start_str, end_str = interval.split('-')
        start = time_to_minutes(start_str)
        end = time_to_minutes(end_str)
        busy_intervals.append((start, end))

# Merge intervals
busy_intervals.sort()
merged = []
for start, end in busy_intervals:
    if not merged:
        merged.append([start, end])
    else:
        last_start, last_end = merged[-1]
        if start <= last_end:
            merged[-1][1] = max(last_end, end)
        else:
            merged.append([start, end])

# Find free intervals within work hours (9:00 to 17:00)
work_start = 9 * 60
work_end = 17 * 60
free_intervals = []

# Check before first busy interval
if merged and merged[0][0] > work_start:
    free_intervals.append([work_start, merged[0][0]])

# Check between merged intervals
for i in range(1, len(merged)):
    prev_end = merged[i-1][1]
    current_start = merged[i][0]
    if current_start > prev_end:
        free_intervals.append([prev_end, current_start])

# Check after last busy interval
if merged and merged[-1][1] < work_end:
    free_intervals.append([merged[-1][1], work_end])

# Handle case with no busy intervals
if not merged:
    free_intervals.append([work_start, work_end])

# Find suitable slots (>=30 minutes)
target_duration = 30
preferred_end = 13 * 60  # 13:00
suitable_slots = []

for start, end in free_intervals:
    if end - start >= target_duration:
        slot_start = start
        slot_end = start + target_duration
        suitable_slots.append((slot_start, slot_end))

# Prioritize slots before preferred_end
valid_slots = [slot for slot in suitable_slots if slot[1] <= preferred_end]
if not valid_slots:
    valid_slots = suitable_slots

# Choose earliest valid slot
chosen_start, chosen_end = min(valid_slots, key=lambda x: x[0])

print(f"Monday:{minutes_to_time(chosen_start)}-{minutes_to_time(chosen_end)}")