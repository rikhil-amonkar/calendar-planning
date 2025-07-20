def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1]) if len(parts) > 1 else 0
    return hours * 60 + minutes

def minutes_to_time(mins):
    hours = mins // 60
    minutes = mins % 60
    return f"{hours:02d}:{minutes:02d}"

# Given constraints
day = "Monday"
work_start = "9:00"
work_end = "17:00"
meeting_duration = 30

# Evelyn: available until 13:00 (so 9:00-13:00)
evelyn_start = time_to_minutes("9:00")
evelyn_end = time_to_minutes("13:00")

# Randy's busy periods (converted to minutes)
randy_busy = [
    (time_to_minutes("9:00"), time_to_minutes("10:30")),
    (time_to_minutes("11:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:00"), time_to_minutes("17:00"))
]

# Calculate Randy's free slots within work hours
work_start_min = time_to_minutes(work_start)
work_end_min = time_to_minutes(work_end)
free_slots = []
current = work_start_min

# Sort busy periods by start time
randy_busy.sort(key=lambda x: x[0])

for start, end in randy_busy:
    if current < start:
        free_slots.append((current, start))
    current = end
if current < work_end_min:
    free_slots.append((current, work_end_min))

# Find a free slot that fits meeting duration and aligns with Evelyn's availability
for slot_start, slot_end in free_slots:
    slot_duration = slot_end - slot_start
    if slot_duration < meeting_duration:
        continue
        
    # Check overlap with Evelyn's availability
    overlap_start = max(slot_start, evelyn_start)
    overlap_end = min(slot_end, evelyn_end)
    if overlap_end - overlap_start >= meeting_duration:
        meeting_start = overlap_start
        meeting_end = meeting_start + meeting_duration
        start_str = minutes_to_time(meeting_start)
        end_str = minutes_to_time(meeting_end)
        print(f"{day} {start_str}:{end_str}")
        break