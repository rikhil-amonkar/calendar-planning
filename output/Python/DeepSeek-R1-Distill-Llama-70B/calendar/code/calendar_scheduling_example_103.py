# Define the schedules for each participant as dictionaries with blocked time slots
schedules = {
    "Diane": [(9, 30, 10, 0), (14, 30, 15, 0)],
    "Jack": [(13, 30, 14, 0), (14, 30, 15, 0)],
    "Eugene": [(9, 0, 10, 0), (10, 30, 11, 30), (12, 0, 14, 30), (15, 0, 16, 30)],
    "Patricia": [(9, 30, 10, 30), (11, 0, 12, 0), (12, 30, 14, 0), (15, 0, 16, 30)]
}

# Function to check if a time slot is available for all participants
def is_available(start_hour, start_minute, end_hour, end_minute, schedules):
    for name, blocks in schedules.items():
        for block in blocks:
            # Convert time to minutes for easier comparison
            block_start = block[0] * 60 + block[1]
            block_end = block[2] * 60 + block[3]
            
            meeting_start = start_hour * 60 + start_minute
            meeting_end = end_hour * 60 + end_minute
            
            # Check if meeting time overlaps with any blocked time
            if not (meeting_end <= block_start or meeting_start >= block_end):
                return False
    return True

# Iterate through possible meeting times (30-minute slots)
for hour in range(9, 17):
    for minute in [0, 30]:
        start_hour, start_minute = hour, minute
        end_hour, end_minute = hour, minute + 30
        
        # Ensure end time doesn't exceed 17:00
        if end_hour > 17 or (end_hour == 17 and end_minute != 0):
            continue
            
        # Check availability for all participants
        if is_available(start_hour, start_minute, end_hour, end_minute, schedules):
            print(f"Proposed time: {start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d} on Monday")
            exit()

# If no time found (shouldn't happen as per problem statement)
print("No available time found.")