from datetime import datetime, timedelta

# Define the meeting duration
meeting_duration = timedelta(minutes=30)

# Define the available slots for both days
monday_slots = [(9, 0, 10, 0), (10, 30, 17, 0)]
tuesday_slots = [(9, 30, 10, 30), (11, 30, 12, 30), (13, 30, 14, 30), (16, 0, 17, 0)]

# Function to check if there is enough time for a meeting in the given slots
def find_meeting_time(slots):
    for start_hour, start_minute, end_hour, end_minute in slots:
        start_time = datetime(2023, 10, 2, start_hour, start_minute)  # Example date only for time calculation
        end_time = datetime(2023, 10, 2, end_hour, end_minute)
        
        if end_time - start_time >= meeting_duration:
            meeting_start = start_time
            meeting_end = meeting_start + meeting_duration
            if meeting_end <= end_time:
                return meeting_start, meeting_end
    return None, None

# Check Monday and Tuesday
monday_meeting_time = find_meeting_time(monday_slots)
tuesday_meeting_time = find_meeting_time(tuesday_slots)

# Select the preferred meeting time
if tuesday_meeting_time[0]:
    proposed_time = tuesday_meeting_time
    day = "Tuesday"
else:
    proposed_time = monday_meeting_time
    day = "Monday"

# Format the output
output_start = proposed_time[0].strftime("%H:%M")
output_end = proposed_time[1].strftime("%H:%M")
output = f"{output_start}:{output_end} on {day}"

print(output)