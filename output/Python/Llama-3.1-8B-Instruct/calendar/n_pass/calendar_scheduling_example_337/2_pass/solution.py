from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.
    
    Parameters:
    participants (dict): A dictionary where the keys are the participant names and the values are lists of tuples representing their meeting times.
    meeting_duration (int): The duration of the meeting in minutes.
    
    Returns:
    tuple: A tuple containing the start and end times of the meeting in HH:MM format and the day of the week.
    """
    
    # Initialize the earliest available time
    earliest_time = datetime.strptime('09:00', '%H:%M')
    
    # Iterate over the participants to find a common available time
    for participant, times in participants.items():
        if not times:  # Check if the participant has no available times
            continue  # Skip the participant if they have no available times
        
        # Sort the participant's available times by their start time
        sorted_times = sorted(times, key=lambda x: x[0])
        
        # Iterate over the participant's available times
        for time in sorted_times:
            start_time = datetime.strptime(time[0], '%H:%M')
            end_time = datetime.strptime(time[1], '%H:%M')
            if start_time >= earliest_time:
                # Check if the meeting can fit in the available time
                meeting_end_time = start_time + timedelta(minutes=meeting_duration)
                if meeting_end_time <= end_time:
                    # Return the meeting time and day
                    return f"{earliest_time.strftime('%H:%M')}:{meeting_end_time.strftime('%H:%M')}", earliest_time.strftime('%A')
                else:
                    # Update the earliest available time
                    earliest_time = end_time + timedelta(minutes=1)
    
    # If no common available time is found, return None
    return None


# Define the participants' schedules
participants = {
    'John': [(11, 30), (12, 0), (14, 0), (14, 30)],
    'Megan': [(12, 0), (12, 30), (14, 0), (15, 0), (15, 30), (16, 0)],
    'Brandon': [],
    'Kimberly': [(9, 0), (9, 30), (10, 0), (10, 30), (11, 0), (14, 30), (15, 0), (16, 0), (16, 30)],
    'Sean': [(10, 0), (11, 0), (11, 30), (14, 0), (15, 0), (15, 30)],
    'Lori': [(9, 0), (9, 30), (10, 30), (12, 0), (13, 0), (14, 30), (16, 0), (16, 30)],
}

# Define the meeting duration
meeting_duration = 30

# Find the meeting time
meeting_time = find_meeting_time(participants, meeting_duration)

# Print the meeting time and day
if meeting_time:
    print(f"Meeting time: {meeting_time[0]}")
    print(f"Day: {meeting_time[1]}")
else:
    print("No common available time found.")