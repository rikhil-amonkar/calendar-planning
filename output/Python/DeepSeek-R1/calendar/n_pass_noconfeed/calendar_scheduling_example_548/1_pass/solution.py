def time_to_minutes(time_str):
    h, m = time_str.split(':')
    return int(h) * 60 + int(m)

def minutes_to_hm(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Given data
work_start = "09:00"
work_end = "17:00"
busy_times = [("09:00", "10:00"), ("10:30", "16:30")]

# Convert to minutes
work_start_min = time_to_minutes(work_start)
work_end_min = time_to_minutes(work_end)
busy_intervals = [(time_to_minutes(s), time_to_minutes(e)) for s, e in busy_times]

# Sort busy intervals by start time
busy_intervals.sort()

# Compute free intervals
free_intervals = []
current = work_start_min
for start, end in busy_intervals:
    if current < start:
        free_intervals.append((current, start))
    current = max(current, end)
if current < work_end_min:
    free_intervals.append((current, work_end_min))

# Find a suitable interval (>=30 minutes and after 16:00 if possible)
candidate = None
preferred_start_min = 16 * 60  # 16:00 in minutes

# First pass: look for intervals starting at or after 16:00
for interval in free_intervals:
    start, end = interval
    if (end - start) >= 30 and start >= preferred_start_min:
        candidate = interval
        break

# Second pass: if no preferred interval, take any suitable interval
if candidate is None:
    for interval in free_intervals:
        start, end = interval
        if (end - start) >= 30:
            candidate = interval
            break

# Schedule meeting at the start of the candidate interval
meeting_start = candidate[0]
meeting_end = meeting_start + 30  # 30-minute meeting

# Format output
start_hm = minutes_to_hm(meeting_start)
end_hm = minutes_to_hm(meeting_end)
s_parts = start_hm.split(':')
e_parts = end_hm.split(':')
time_output = f"{s_parts[0]}:{s_parts[1]}:{e_parts[0]}:{e_parts[1]}"

print("Monday", time_output)