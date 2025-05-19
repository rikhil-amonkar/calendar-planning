# Define the work hours and meeting duration
work_start = "09:00"
work_end = "17:00"
meeting_duration = 30  # in minutes

# Define participants' schedules
participants = {
    "Megan": [("09:00", "09:30"), ("10:00", "11:00"), ("12:00", "12:30")],
    "Christine": [("09:00", "09:30"), ("11:30", "12:00"), ("13:00", "14:00"), ("15:30", "16:30")],
    "Gabriel": [],
    "Sara": [("11:30", "12:00"), ("14:30", "15:00")],
    "Bruce": [("09:30", "10:00"), ("10:30", "12:00"), ("12:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:30")],
    "Kathryn": [("10:00", "15:30"), ("16:00", "16:30")],
    "Billy": [("09:00", "09:30"), ("11:00", "11:30"), ("12:00", "14:00"), ("14:30", "15:30")]
}

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

# Initialize available time as the entire work day
available_start = work_start_minutes
available_end = work_end_minutes

# Iterate through each participant's schedule to find common free time
for name, schedule in participants.items():
    # Sort the schedule by start time
    sorted_schedule = sorted(schedule, key=lambda x: time_to_minutes(x[0]))
    
    # Initialize with the work start time
    current_start = work_start_minutes
    
    for slot in sorted_schedule:
        slot_start = time_to_minutes(slot[0])
        slot_end = time_to_minutes(slot[1])
        
        # If the slot starts after the current available start, update the available start
        if slot_start > current_start:
            current_start = max(current_start, slot_end)
    
    # Update the overall available time
    available_start = max(available_start, current_start)

# Ensure the meeting time is within work hours
if available_start + meeting_duration > work_end_minutes:
    print("No available time slot found within constraints.")
else:
    meeting_start = available_start
    meeting_end = meeting_start + meeting_duration
    print(f"Proposed meeting time: {minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)} on Monday")