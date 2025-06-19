from datetime import datetime, timedelta

def schedule_meeting(start_time, end_time, duration, schedules):
    """
    Schedule a meeting between the given start and end time with the specified duration.
    
    Args:
    start_time (str): The start time of the day in the format 'HH:MM'.
    end_time (str): The end time of the day in the format 'HH:MM'.
    duration (int): The duration of the meeting in minutes.
    schedules (dict): A dictionary of participant schedules where the key is the participant's name and the value is a list of time slots they are busy.
    
    Returns:
    str: A string representing the proposed meeting time in the format 'HH:MM:HH:MM' and the day of the week.
    """
    
    # Convert the start and end time to datetime objects
    start_time = datetime.strptime(start_time, '%H:%M')
    end_time = datetime.strptime(end_time, '%H:%M')
    
    # Initialize the meeting time to the start of the day
    meeting_time = start_time
    
    # Loop until we find a meeting time that works for everyone
    while meeting_time < end_time:
        # Check if the meeting time works for everyone
        works_for_everyone = True
        for schedule in schedules.values():
            for time_slot in schedule:
                # Convert the time_slot to a string in the format 'HH:MM'
                time_slot_str = f"{time_slot[0]}:{time_slot[1]}"
                start, end = map(lambda x: datetime.strptime(x, '%H:%M'), [time_slot_str, time_slot_str])
                if meeting_time < end and meeting_time + timedelta(minutes=duration) > start:
                    works_for_everyone = False
                    break
            if not works_for_everyone:
                break
        
        if works_for_everyone:
            # If the meeting time works for everyone, return it
            return f"{meeting_time.strftime('%H:%M')}:{(meeting_time + timedelta(minutes=duration)).strftime('%H:%M')} {start_time.strftime('%A')}"
        
        # If the meeting time does not work for everyone, move to the next time slot
        meeting_time += timedelta(minutes=30)
    
    # If we cannot find a meeting time that works for everyone, return a message indicating that
    return "No meeting time found that works for everyone."


# Define the schedules for each participant
schedules = {
    'Judy': [(13, 30), (16, 30)],
    'Olivia': [(10, 30), (12, 0), (14, 30)],
    'Eric': [],
    'Jacqueline': [(10, 30), (15, 30)],
    'Laura': [(9, 0), (10, 0), (10, 30), (13, 0), (13, 30), (14, 30), (15, 30)],
    'Tyler': [(9, 0), (11, 0), (11, 30), (12, 30), (13, 0), (14, 30), (15, 30)],
    'Lisa': [(9, 30), (10, 30), (11, 0), (11, 30), (12, 0), (12, 30), (13, 0), (13, 30), (14, 0), (14, 30), (16, 0)]
}

# Define the start and end time of the day
start_time = '09:00'
end_time = '17:00'

# Define the meeting duration
duration = 30

# Call the schedule_meeting function to find a meeting time that works for everyone
print(schedule_meeting(start_time, end_time, duration, schedules))