# Define the work hours and constraints
work_start = 9 * 60  # Convert 9:00 AM to minutes since midnight
work_end = 17 * 60   # Convert 5:00 PM to minutes since midnight

# Albert's blocked times in minutes since midnight
albert_blocked_times = [
    (9 * 60, 10 * 60),      # 9:00 AM - 10:00 AM
    (10 * 60 + 30, 12 * 60),  # 10:30 AM - 12:00 PM
    (15 * 60, 16 * 60 + 30)   # 3:00 PM - 4:30 PM
]

# Albert's maximum availability time in minutes since midnight
albert_max_availability = 11 * 60  # 11:00 AM

# Meeting duration in minutes
meeting_duration = 30

# Initialize the start time for checking available slots
current_time = work_start

# Function to convert minutes since midnight to HH:MM format
def minutes_to_hhmm(minutes):
    return f"{minutes // 60:02}:{minutes % 60:02}"

# Find the first available slot for Albert that fits the meeting duration
while current_time < work_end:
    # Check if current_time is within any of Albert's blocked times
    is_blocked = False
    for start, end in albert_blocked_times:
        if start <= current_time < end:
            current_time = end  # Skip to the end of the blocked period
            is_blocked = True
            break
    
    # If the time is not blocked and within Albert's max availability
    if not is_blocked and current_time + meeting_duration <= albert_max_availability:
        # Found a suitable time slot
        meeting_start = current_time
        meeting_end = current_time + meeting_duration
        break
    
    # Move to the next possible start time
    current_time += 1

# Output the result in the required format
print(f"{minutes_to_hhmm(meeting_start)}:{minutes_to_hhmm(meeting_end)} Monday")