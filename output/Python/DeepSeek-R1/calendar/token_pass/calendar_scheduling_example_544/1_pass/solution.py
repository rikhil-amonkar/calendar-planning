# Define work hours and constraints for Albert
work_start_min = 9 * 60  # 9:00 in minutes from midnight
work_end_min = 11 * 60   # 11:00 in minutes, since Albert cannot meet after 11:00

# Albert's blocked intervals in minutes (start, end) where end is exclusive
blocked_intervals = [
    (9 * 60, 10 * 60),      # 9:00 to 10:00
    (10 * 60 + 30, 12 * 60) # 10:30 to 12:00
]

# Find free intervals for Albert within work hours
free_slots = []
current_time = work_start_min

for block_start, block_end in blocked_intervals:
    if block_start >= work_end_min:
        break
    if block_end <= current_time:
        continue
    if current_time < block_start:
        free_slots.append((current_time, block_start))
    current_time = max(current_time, block_end)

if current_time < work_end_min:
    free_slots.append((current_time, work_end_min))

# Meeting duration in minutes
meeting_duration = 30

# Find a free slot that can accommodate the meeting
for slot_start, slot_end in free_slots:
    if slot_end - slot_start >= meeting_duration:
        meeting_start = slot_start
        meeting_end = meeting_start + meeting_duration
        # Convert minutes to time strings
        start_hour = meeting_start // 60
        start_minute = meeting_start % 60
        end_hour = meeting_end // 60
        end_minute = meeting_end % 60
        time_range = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(f"Monday: {time_range}")
        break
else:
    print("No suitable time found")