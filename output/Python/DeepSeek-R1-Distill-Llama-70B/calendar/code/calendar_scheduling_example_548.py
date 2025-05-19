# Define the work hours and meeting duration
work_start = "09:00"
work_end = "17:00"
meeting_duration = 30  # in minutes

# Define participants' schedules and preferences
judy_schedule = []  # Judy is free all day
nicole_schedule = [
    ("09:00", "10:00"),
    ("10:30", "16:30")
]
nicole_preference = "16:00"  # Prefer not before this time

# Convert time strings to minutes since midnight for easier calculations
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

# Convert minutes back to HH:MM format
def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

# Find the earliest available time slot that fits all constraints
work_start_minutes = time_to_minutes(work_start)
work_end_minutes = time_to_minutes(work_end)
meeting_end_minutes = work_start_minutes + meeting_duration

# Check Nicole's availability after her preference time
preference_minutes = time_to_minutes(nicole_preference)
available_start = max(work_start_minutes, preference_minutes)
available_end = work_end_minutes

# Check for available slots in Nicole's schedule
for slot in nicole_schedule:
    slot_start = time_to_minutes(slot[0])
    slot_end = time_to_minutes(slot[1])
    
    if slot_end < available_start:
        continue  # Slot is before the preferred time
    elif slot_start > available_end:
        break  # No more relevant slots
    
    # Adjust available time around this slot
    if slot_start > available_start:
        available_start = slot_end

# Ensure the meeting time is within work hours
if available_start + meeting_duration > available_end:
    print("No available time slot found within constraints.")
else:
    meeting_start = available_start
    meeting_end = meeting_start + meeting_duration
    print(f"Proposed meeting time: {minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)} on Monday")
```