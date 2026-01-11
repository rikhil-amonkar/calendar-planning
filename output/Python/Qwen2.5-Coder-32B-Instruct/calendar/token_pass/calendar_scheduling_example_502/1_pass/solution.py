from datetime import datetime, timedelta

def find_meeting_time(jack_busy_times, charlotte_busy_times, meeting_duration, preferred_end_time):
    # Define work hours
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    # Convert busy times to datetime objects
    jack_busy_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in jack_busy_times]
    charlotte_busy_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in charlotte_busy_times]
    
    # Combine all busy times
    all_busy_times = sorted(jack_busy_times + charlotte_busy_times)
    
    # Initialize variables to track the current time
    current_time = work_start
    
    # Iterate through work hours to find a free slot
    while current_time < work_end - meeting_duration:
        # Check if current time is within any busy time
        free = True
        for busy_start, busy_end in all_busy_times:
            if current_time >= busy_start and current_time < busy_end:
                free = False
                current_time = busy_end  # Skip to the end of the busy period
                break
        
        # If the current time is free, check if the slot fits the meeting duration
        if free:
            meeting_end = current_time + meeting_duration
            if meeting_end <= work_end:
                # Check if the meeting ends before the preferred end time or if no other options are available
                if meeting_end <= preferred_end_time or current_time >= preferred_end_time:
                    return current_time.strftime("%H:%M"), meeting_end.strftime("%H:%M"), "Monday"
        
        # Move to the next possible start time
        current_time += timedelta(minutes=1)
    
    return None

# Define busy times
jack_busy_times = [("09:30", "10:30"), ("11:00", "11:30"), ("12:30", "13:00"), ("14:00", "14:30"), ("16:00", "16:30")]
charlotte_busy_times = [("09:30", "10:00"), ("10:30", "12:00"), ("12:30", "13:30"), ("14:00", "16:00")]

# Define meeting duration (30 minutes)
meeting_duration = timedelta(minutes=30)

# Define Jack's preferred end time (12:30 PM)
preferred_end_time = datetime.strptime("12:30", "%H:%M")

# Find a suitable meeting time
meeting_time = find_meeting_time(jack_busy_times, charlotte_busy_times, meeting_duration, preferred_end_time)

if meeting_time:
    print(f"Meeting Time: {meeting_time[0]}:{meeting_time[1]}, Day: {meeting_time[2]}")
else:
    print("No suitable meeting time found.")