def time_to_minutes(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30
day = "Monday"

# Albert's busy time blocks in minutes (start, end)
albert_busy = [
    (time_to_minutes("09:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("12:00")),
    (time_to_minutes("15:00"), time_to_minutes("16:30"))
]

# Albert can't meet after 11:00
max_end_time = time_to_minutes("11:00")

# Generate free slots considering work hours and busy times
free_slots = []
previous_end = work_start

for start, end in sorted(albert_busy + [(work_end, work_end)]):
    if start > previous_end:
        free_start = previous_end
        free_end = min(start, max_end_time)
        if free_end > free_start:
            free_slots.append((free_start, free_end))
    previous_end = max(previous_end, end)

# Find the first slot that can accommodate the meeting
for slot_start, slot_end in free_slots:
    if slot_end - slot_start >= meeting_duration:
        meeting_start = slot_start
        meeting_end = meeting_start + meeting_duration
        # Ensure meeting doesn't exceed the allowed end time
        if meeting_end <= max_end_time:
            print(f"{day}:{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
            exit()

# Fallback (though problem states a solution exists)
print("No suitable time found")