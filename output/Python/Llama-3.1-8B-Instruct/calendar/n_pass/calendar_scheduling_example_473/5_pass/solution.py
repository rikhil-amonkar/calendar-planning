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
    start_times = [min(times) for times in participants.values()]
    end_times = [max(times) for times in participants.values()]
    
    # Find the earliest start time
    earliest_start_time = min(start_times)
    
    # Calculate the earliest possible meeting time
    earliest_start_hour = earliest_start_time // 60
    earliest_start_minute = earliest_start_time % 60
    
    # Try all possible meeting times
    for hour in range(earliest_start_hour, 24):
        for minute in range(earliest_start_minute, 60, meeting_duration):
            meeting_time = datetime(2025, 6, 19, hour, minute)  # Assuming the meeting is on June 19, 2025
            
            # Check if the meeting time works for all participants
            if all(not any((meeting_time >= datetime(start_year, start_month, start_day, start_hour, start_minute) < meeting_time + timedelta(minutes=meeting_duration)) for start_year, start_month, start_day, start_hour, start_minute in times) for times in participants.values()):
                return datetime.strftime(meeting_time, "%A"), datetime.strftime(meeting_time, "%H:%M") + "-" + datetime.strftime(meeting_time + timedelta(minutes=meeting_duration-1), "%H:%M")
    
    # If no meeting time is found, return a message
    return "No meeting time found"

# Define the participants and their busy times
participants = {
    "Gregory": [(9 * 60 + 30), (11 * 60 + 30, 12 * 60 + 0)],
    "Jonathan": [(9 * 60 + 30), (12 * 60 + 0, 12 * 60 + 30), (13 * 60 + 0, 13 * 60 + 30), (15 * 60 + 0, 16 * 60 + 0), (16 * 60 + 30, 17 * 60 + 0)],
    "Barbara": [(10 * 60 + 0, 10 * 60 + 30), (13 * 60 + 30, 14 * 60 + 0)],
    "Jesse": [(10 * 60 + 0, 11 * 60 + 0), (12 * 60 + 30, 14 * 60 + 30)],
    "Alan": [(9 * 60 + 30, 11 * 60 + 0), (11 * 60 + 30, 12 * 60 + 30), (13 * 60 + 0, 15 * 60 + 30), (16 * 60 + 0, 17 * 60 + 0)],
    "Nicole": [(9 * 60 + 0, 10 * 60 + 30), (11 * 60 + 30, 12 * 60 + 0), (12 * 60 + 30, 13 * 60 + 30), (14 * 60 + 0, 17 * 60 + 0)],
    "Catherine": [(9 * 60 + 0, 10 * 60 + 30), (12 * 60 + 0, 13 * 60 + 30), (15 * 60 + 0, 15 * 60 + 30), (16 * 60 + 0, 16 * 60 + 30)]
}

# Define the meeting duration
meeting_duration = 30

# Find a meeting time that works for everyone
day, time = find_meeting_time(participants, meeting_duration)

# Print the result
print(f"Day: {day}")
print(f"Time: {time}")