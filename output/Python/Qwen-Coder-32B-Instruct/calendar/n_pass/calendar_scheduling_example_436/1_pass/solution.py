from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, start_time, end_time):
    # Convert start and end times to datetime objects
    start = datetime.strptime(start_time, "%H:%M")
    end = datetime.strptime(end_time, "%H:%M")
    
    # Initialize a list to keep track of available times
    available_times = []
    
    # Iterate over each minute in the workday
    current_time = start
    while current_time + timedelta(minutes=meeting_duration) <= end:
        # Check if all participants are available at the current time
        all_available = True
        for person_schedule in schedules.values():
            for busy_start, busy_end in person_schedule:
                busy_start_dt = datetime.strptime(busy_start, "%H:%M")
                busy_end_dt = datetime.strptime(busy_end, "%H:%M")
                if busy_start_dt <= current_time < busy_end_dt or busy_start_dt < current_time + timedelta(minutes=meeting_duration) <= busy_end_dt:
                    all_available = False
                    break
            if not all_available:
                break
        
        # If all participants are available, add this time slot to the list
        if all_available:
            available_times.append((current_time.strftime("%H:%M"), (current_time + timedelta(minutes=meeting_duration)).strftime("%H:%M")))
        
        # Move to the next minute
        current_time += timedelta(minutes=1)
    
    # Return the first available time slot found
    if available_times:
        return available_times[0]
    else:
        return None

# Define the schedules for each participant
schedules = {
    "Patrick": [("13:30", "14:00"), ("14:30", "15:00")],
    "Shirley": [("9:00", "9:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("14:30", "15:00"), ("16:00", "17:00")],
    "Jeffrey": [("9:00", "9:30"), ("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("16:00", "17:00")],
    "Gloria": [("11:30", "12:00"), ("15:00", "15:30")],
    "Nathan": [("9:00", "9:30"), ("10:30", "12:00"), ("14:00", "17:00")],
    "Angela": [("9:00", "9:30"), ("10:00", "11:00"), ("12:30", "15:00"), ("15:30", "16:30")],
    "David": [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "14:00"), ("14:30", "16:30")]
}

# Define the meeting duration and work hours
meeting_duration = 30
start_time = "9:00"
end_time = "17:00"

# Find the meeting time
meeting_time = find_meeting_time(schedules, meeting_duration, start_time, end_time)

# Output the result
if meeting_time:
    print(f"{meeting_time[0]}:{meeting_time[1]} Monday")
else:
    print("No available time found.")