# Define the work hours and constraints
work_start = 9 * 60  # Convert 9:00 to minutes since start of the day
work_end = 17 * 60   # Convert 17:00 to minutes since start of the day

# Judy's availability (entire day)
judy_free_slots = [(work_start, work_end)]

# Nicole's busy slots
nicole_busy_slots = [(9 * 60, 10 * 60), (10 * 60 + 30, 16 * 60 + 30)]

# Calculate Nicole's free slots
nicole_free_slots = []
current_time = work_start
for start, end in nicole_busy_slots:
    if current_time < start:
        nicole_free_slots.append((current_time, start))
    current_time = max(current_time, end)
if current_time < work_end:
    nicole_free_slots.append((current_time, work_end))

# Consider Nicole's preference to not meet before 16:00
preferred_start = 16 * 60  # Convert 16:00 to minutes since start of the day
nicole_preferred_free_slots = [slot for slot in nicole_free_slots if slot[0] >= preferred_start]

# Find a common slot between Judy and Nicole that is at least 30 minutes long
meeting_duration = 30  # 30 minutes
for j_start, j_end in judy_free_slots:
    for n_start, n_end in nicole_preferred_free_slots:
        common_start = max(j_start, n_start)
        common_end = min(j_end, n_end)
        if common_end - common_start >= meeting_duration:
            # Found a suitable slot
            meeting_start = common_start
            meeting_end = meeting_start + meeting_duration
            break
    else:
        continue
    break

# Convert meeting time back to HH:MM format
def convert_to_hhmm(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02}:{minutes:02}"

meeting_start_hhmm = convert_to_hhmm(meeting_start)
meeting_end_hhmm = convert_to_hhmm(meeting_end)

# Output the result
print(f"Meeting time: {meeting_start_hhmm}:{meeting_end_hhmm} on Monday")