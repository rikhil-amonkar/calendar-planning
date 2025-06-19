from datetime import datetime, timedelta

def find_meeting_time(participant_schedules, meeting_duration, preferences):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
        participant_schedules (dict): A dictionary where keys are participant names and values are lists of tuples representing their schedules.
        meeting_duration (int): The duration of the meeting in minutes.
        preferences (dict): A dictionary where keys are participant names and values are lists of tuples representing their preferred meeting times.

    Returns:
        tuple: A tuple containing the day of the week and the proposed meeting time in the format HH:MM - HH:MM.
    """

    # Get the current date
    current_date = datetime.now()

    # Iterate over each participant's schedules
    for participant, schedules in participant_schedules.items():
        # Iterate over each schedule of the participant
        for schedule in schedules:
            start_time = schedule[0]
            end_time = schedule[1]

            # Calculate the end time of the meeting
            meeting_end_time = start_time + timedelta(minutes=meeting_duration)

            # Check if the meeting time is within the participant's schedule and preferences
            if (start_time >= datetime(current_date.year, current_date.month, current_date.day, 9, 0) and 
                start_time < datetime(current_date.year, current_date.month, current_date.day, 17, 0)) and \
               (meeting_end_time >= datetime(current_date.year, current_date.month, current_date.day, 9, 0) and 
                meeting_end_time <= datetime(current_date.year, current_date.month, current_date.day, 17, 0)):
                # Check if the time slot is available for other participants
                for other_participant, other_schedules in participant_schedules.items():
                    if other_participant!= participant:
                        for other_schedule in other_schedules:
                            if (start_time < other_schedule[0] < meeting_end_time or 
                                start_time < other_schedule[1] < meeting_end_time or 
                                start_time > other_schedule[0] and start_time < other_schedule[1] or 
                                meeting_end_time > other_schedule[0] and meeting_end_time < other_schedule[1]):
                                # If the time slot is not available, skip to the next schedule
                                break
                        else:
                            # If the time slot is available for all participants, check if it meets the preferences
                            if participant in preferences and any(start_time >= preferred_time[0] and meeting_end_time <= preferred_time[1] for preferred_time in preferences[participant]):
                                # If the time slot meets the preferences, return the proposed meeting time
                                return current_date.strftime("%A"), f"{start_time.strftime('%H:%M')} - {meeting_end_time.strftime('%H:%M')}"

    # If no available time slot is found, return a message indicating that no suitable time was found
    return "No suitable time found", "N/A"


# Example usage
participant_schedules = {
    "Evelyn": [(datetime(2024, 7, 22, 9, 0), datetime(2024, 7, 22, 17, 0))],
    "Randy": [(datetime(2024, 7, 22, 9, 0), datetime(2024, 7, 22, 10, 30)),
              (datetime(2024, 7, 22, 11, 0), datetime(2024, 7, 22, 15, 30)),
              (datetime(2024, 7, 22, 16, 0), datetime(2024, 7, 22, 17, 0))]
}

meeting_duration = 30  # minutes
preferences = {
    "Evelyn": [(datetime(2024, 7, 22, 9, 0), datetime(2024, 7, 22, 13, 0))],
    "Randy": [(datetime(2024, 7, 22, 9, 0), datetime(2024, 7, 22, 13, 0))]
}

day, proposed_time = find_meeting_time(participant_schedules, meeting_duration, preferences)
print(f"Proposed meeting time: {proposed_time} on {day}")