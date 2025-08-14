def to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def from_minutes(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

work_start = to_minutes("9:00")
work_end = to_minutes("17:00")
meeting_duration = 30  # minutes
nicole_busy = [("9:00", "10:00"), ("10:30", "16:30")]
preference_after = to_minutes("16:00")

# Convert Nicole's busy times to minutes
busy = []
for start, end in nicole_busy:
    busy.append((to_minutes(start), to_minutes(end)))

sorted_busy = sorted(busy, key=lambda x: x[0])

# Compute free intervals
free_intervals = []
prev_end = work_start
for start, end in sorted_busy:
    if start > prev_end:
        free_intervals.append((prev_end, start))
    prev_end = max(prev_end, end)

# Check after last busy
if prev_end < work_end:
    free_intervals.append((prev_end, work_end))

# Filter valid slots
valid_slots = []
for start, end in free_intervals:
    duration = end - start
    if duration >= meeting_duration:
        if start >= preference_after:
            valid_slots.append((start, end))

# Select the first valid slot
selected_start = valid_slots[0][0]
selected_end = selected_start + meeting_duration

start_time_str = from_minutes(selected_start)
end_time_str = from_minutes(selected_end)
day = "Monday"

print(f"{start_time_str}:{end_time_str} {day}")