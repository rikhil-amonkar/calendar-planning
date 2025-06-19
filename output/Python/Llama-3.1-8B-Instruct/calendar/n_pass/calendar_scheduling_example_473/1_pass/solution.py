from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration):
    """
    Find a time that works for everyone's schedule and constraints.
    
    Args:
    participants (dict): A dictionary where keys are participant names and values are lists of tuples representing their busy times.
    meeting_duration (int): The duration of the meeting in minutes.
    
    Returns:
    tuple: A tuple containing the day of the week and a string representing the meeting time in the format HH:MM-HH:MM.
    """
    
    # Find the earliest start time and latest end time for all participants
    start_time = min([min(times) for times in participants.values()])
    end_time = max([max(times) for times in participants.values()])
    
    # Calculate the earliest possible meeting time
    earliest_meeting_time = start_time + timedelta(minutes=meeting_duration)
    
    # Try all possible meeting times
    for hour in range(start_time.hour, end_time.hour):
        for minute in range(0, 60, meeting_duration):
            meeting_time = datetime(start_time.year, start_time.month, start_time.day, hour, minute)
            
            # Check if the meeting time works for all participants
            if all(not any(meeting_time >= datetime(start_year, start_month, start_day, start_hour, start_minute) < meeting_time + timedelta(minutes=meeting_duration) for start_year, start_month, start_day, start_hour, start_minute in times) for times in participants.values()):
                return datetime.strftime(meeting_time, "%A"), datetime.strftime(meeting_time, "%H:%M") + "-" + datetime.strftime(meeting_time + timedelta(minutes=meeting_duration-1), "%H:%M")
    
    # If no meeting time is found, return a message
    return "No meeting time found"

# Define the participants and their busy times
participants = {
    "Gregory": [(9, 30), (11, 30, 12, 0)],
    "Jonathan": [(9, 30), (12, 0, 12, 30), (13, 0, 13, 30), (15, 0, 16, 0), (16, 30, 17, 0)],
    "Barbara": [(10, 0, 10, 30), (13, 30, 14, 0)],
    "Jesse": [(10, 0, 11, 0), (12, 30, 14, 30)],
    "Alan": [(9, 30, 11, 0), (11, 30, 12, 30), (13, 0, 15, 30), (16, 0, 17, 0)],
    "Nicole": [(9, 0, 10, 30), (11, 30, 12, 0), (12, 30, 13, 30), (14, 0, 17, 0)],
    "Catherine": [(9, 0, 10, 30), (12, 0, 13, 30), (15, 0, 15, 30), (16, 0, 16, 30)]
}

# Define the meeting duration
meeting_duration = 30

# Find a meeting time that works for everyone
day, time = find_meeting_time(participants, meeting_duration)

# Print the result
print(f"Day: {day}")
print(f"Time: {time}")