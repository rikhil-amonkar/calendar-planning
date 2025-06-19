from datetime import datetime, timedelta

def schedule_meeting(start_time, end_time, meeting_duration, participants, preferences):
    """
    Schedule a meeting between the given participants within the specified time frame.
    
    Args:
        start_time (datetime): The start time of the workday.
        end_time (datetime): The end time of the workday.
        meeting_duration (int): The duration of the meeting in minutes.
        participants (dict): A dictionary where the keys are participant names and the values are lists of their busy times.
        preferences (dict): A dictionary where the keys are participant names and the values are their meeting time preferences.
    
    Returns:
        str: A string in the format "Day: HH:MM-HH:MM" representing the proposed meeting time.
    """

    # Sort the participants by their meeting time preferences
    sorted_participants = sorted(participants.items(), key=lambda x: preferences.get(x[0], datetime.max))

    # Find the earliest available time slot that can accommodate the meeting
    for hour in range(start_time.hour, end_time.hour):
        for minute in range(0, 60, meeting_duration):
            time = start_time.replace(hour=hour, minute=minute)
            if is_available(participants, time, time + timedelta(minutes=meeting_duration), preferences, start_time, end_time):
                return f"{time.strftime('%A')}: {time.strftime('%H:%M')}-{(time + timedelta(minutes=meeting_duration)).strftime('%H:%M')}"

    # If no time slot is found, return a message indicating that
    return "No available time slot found."


def is_available(participants, start_time, end_time, preferences, start_of_workday, end_of_workday):
    """
    Check if a given time slot is available for all participants.
    
    Args:
        participants (dict): A dictionary where the keys are participant names and the values are lists of their busy times.
        start_time (datetime): The start time of the time slot.
        end_time (datetime): The end time of the time slot.
        preferences (dict): A dictionary where the keys are participant names and the values are their meeting time preferences.
        start_of_workday (datetime): The start time of the workday.
        end_of_workday (datetime): The end time of the workday.
    
    Returns:
        bool: True if the time slot is available for all participants, False otherwise.
    """

    # Check if the time slot is within the workday
    if start_time < start_of_workday or end_time > end_of_workday:
        return False

    # Check if the time slot is available for each participant
    for participant, busy_times in participants.items():
        # Check if the participant has a meeting time preference
        preferred_time = preferences.get(participant, datetime.max)
        
        # Check if the participant's preferred time is within the workday
        if preferred_time < start_of_workday or preferred_time > end_of_workday:
            # If the participant's preferred time is not within the workday, ignore it
            continue
        
        # Check if the participant's busy times overlap with the time slot
        for busy_time in busy_times:
            if start_time < busy_time + timedelta(minutes=1) and end_time > busy_time:
                # If the participant's busy times overlap with the time slot, return False
                return False
        
        # Check if the participant's preferred time overlaps with the time slot
        if start_time < preferred_time + timedelta(minutes=1) and end_time > preferred_time:
            # If the participant's preferred time overlaps with the time slot, return False
            return False

    # If the time slot is available for all participants, return True
    return True


def main():
    # Define the start and end times of the workday
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')

    # Define the meeting duration
    meeting_duration = 30

    # Define the participants and their busy times
    participants = {
        'Jose': [datetime.strptime('11:00', '%H:%M'), datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:00', '%H:%M')],
        'Keith': [datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M')],
        'Logan': [datetime.strptime('09:00', '%H:%M'), datetime.strptime('10:00', '%H:%M'), datetime.strptime('12:00', '%H:%M'), datetime.strptime('12:30', '%H:%M'), datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M')],
        'Megan': [datetime.strptime('09:00', '%H:%M'), datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M'), datetime.strptime('12:00', '%H:%M'), datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:30', '%H:%M'), datetime.strptime('16:30', '%H:%M')],
        'Gary': [datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:00', '%H:%M'), datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:30', '%H:%M'), datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M'), datetime.strptime('16:30', '%H:%M')],
        'Bobby': [datetime.strptime('11:00', '%H:%M'), datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M'), datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:00', '%H:%M'), datetime.strptime('16:00', '%H:%M')]
    }

    # Define the participant preferences
    preferences = {
        'Jose': datetime.strptime('15:30', '%H:%M')
    }

    # Schedule the meeting
    proposed_time = schedule_meeting(start_time, end_time, meeting_duration, participants, preferences)

    # Print the proposed meeting time
    print(proposed_time)


if __name__ == "__main__":
    main()