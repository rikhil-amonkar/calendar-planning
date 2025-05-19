# Define the schedules for each participant as dictionaries with blocked time slots
schedules = {
    "Martha": {
        "Monday": [(16, 0, 17, 0)],
        "Tuesday": [(15, 0, 15, 30)],
        "Wednesday": [(10, 0, 11, 0), (14, 0, 14, 30)]
    },
    "Beverly": {
        "Monday": [(9, 0, 13, 30), (14, 0, 17, 0)],
        "Tuesday": [(9, 0, 17, 0)],
        "Wednesday": [(9, 30, 15, 30), (16, 30, 17, 0)]
    }
}

# Function to check if a time slot is available for all participants on a given day
def is_available(day, start_hour, start_minute, end_hour, end_minute, schedules):
    for name, days in schedules.items():
        for block in days.get(day, []):
            # Convert time to minutes for easier comparison
            block_start = block[0] * 60 + block[1]
            block_end = block[2] * 60 + block[3]
            
            meeting_start = start_hour * 60 + start_minute
            meeting_end = end_hour * 60 + end_minute
            
            # Check if meeting time overlaps with any blocked time
            if not (meeting_end <= block_start or meeting_start >= block_end):
                return False
    return True

# Iterate through possible days
days = ["Monday", "Tuesday", "Wednesday"]
for day in days:
    # Iterate through possible start times (on the hour and half past)
    for hour in range(9, 17):
        for minute in [0, 30]:
            start_hour, start_minute = hour, minute
            end_hour, end_minute = hour, minute + 30
            
            # Ensure end time doesn't exceed 17:00
            if end_hour > 17 or (end_hour == 17 and end_minute != 0):
                continue
                
            # Check availability for all participants
            if is_available(day, start_hour, start_minute, end_hour, end_minute, schedules):
                print(f"Proposed time: {start_hour:02d}:{start_minute:02d}-{end_hour:02d}:{end_minute:02d} on {day}")
                exit()

# If no time found (shouldn't happen as per problem statement)
print("No available time found.")