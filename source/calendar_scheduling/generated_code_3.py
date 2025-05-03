from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, duration, schedules, preferences):
    """
    Find a time that works for everyone's schedule and constraints.
    
    Args:
    start_time (datetime): The start time of the work hours.
    end_time (datetime): The end time of the work hours.
    duration (timedelta): The duration of the meeting.
    schedules (dict): A dictionary where the keys are the participants' names and the values are their schedules.
    preferences (dict): A dictionary where the keys are the participants' names and the values are their preferences.
    
    Returns:
    tuple: A tuple containing the start and end time of the meeting.
    """
    # Sort the schedules by their start time
    sorted_schedules = sorted(schedules.items(), key=lambda x: x[1][0])
    
    # Initialize the meeting time to the start of the work hours
    meeting_start = start_time
    
    # Loop until we find a time that works for everyone
    while meeting_start < end_time:
        # Check if the meeting time works for everyone
        if all(meeting_start + duration <= schedule[1][-1] for name, schedule in sorted_schedules):
            # If it does, check if Rachel prefers to meet after 13:00
            if preferences.get("Rachel", None) == "prefer_after_13:00" and meeting_start < datetime(2024, 7, 22, 13, 0):
                # If Rachel prefers to meet after 13:00, move to the next available time
                for name, schedule in sorted_schedules:
                    if meeting_start + duration > schedule[1][-1]:
                        meeting_start = schedule[1][-1] + timedelta(minutes=1)
                        break
                # If we've reached the end of the work hours, move to the next day
                if meeting_start > end_time:
                    meeting_start = start_time.replace(hour=9, minute=0)
            else:
                # If it does, return the meeting time
                return meeting_start.strftime("%H:%M"), (meeting_start + duration).strftime("%H:%M")
        
        # If it doesn't, move the meeting time to the next available time
        for name, schedule in sorted_schedules:
            if meeting_start + duration > schedule[1][-1]:
                meeting_start = schedule[1][-1] + timedelta(minutes=1)
                break
        
        # If we've reached the end of the work hours, move to the next day
        if meeting_start > end_time:
            meeting_start = start_time.replace(hour=9, minute=0)
    
    # If we've reached this point, it means that there's no time that works for everyone
    return None

# Define the schedules
schedules = {
    "Rachel": [(datetime(2024, 7, 22, 12, 0), datetime(2024, 7, 22, 12, 30)), (datetime(2024, 7, 22, 14, 0), datetime(2024, 7, 22, 14, 30)), (datetime(2024, 7, 22, 15, 30), datetime(2024, 7, 22, 16, 0)), (datetime(2024, 7, 22, 16, 30), datetime(2024, 7, 22, 17, 0))],
    "Wayne": [(datetime(2024, 7, 22, 9, 0), datetime(2024, 7, 22, 9, 30)), (datetime(2024, 7, 22, 10, 0), datetime(2024, 7, 22, 10, 30)), (datetime(2024, 7, 22, 11, 0), datetime(2024, 7, 22, 14, 30)), (datetime(2024, 7, 22, 15, 0), datetime(2024, 7, 22, 15, 30)), (datetime(2024, 7, 22, 16, 0), datetime(2024, 7, 22, 17, 0))]
}

# Define the preferences
preferences = {
    "Rachel": "prefer_after_13:00"
}

# Define the start and end time of the work hours
start_time = datetime(2024, 7, 22, 9, 0)
end_time = datetime(2024, 7, 22, 17, 0)

# Define the duration of the meeting
duration = timedelta(minutes=30)

# Find a time that works for everyone
meeting_start, meeting_end = find_meeting_time(start_time, end_time, duration, schedules, preferences)

# Print the meeting time
if meeting_start is not None:
    print(f"{meeting_start}-{meeting_end}")
else:
    print("No time found")