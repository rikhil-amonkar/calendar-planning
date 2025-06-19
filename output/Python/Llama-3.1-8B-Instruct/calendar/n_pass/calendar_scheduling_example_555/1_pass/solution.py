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

    # Find the first available time slot for the first participant
    first_participant = list(participant_schedules.keys())[0]
    first_participant_schedules = participant_schedules[first_participant]

    # Iterate over the schedules of the first participant to find the first available time slot
    for i in range(len(first_participant_schedules) - 1):
        start_time = first_participant_schedules[i][1]
        end_time = first_participant_schedules[i + 1][0]

        # Check if the time slot is available for the first participant and other participants
        for participant, schedules in participant_schedules.items():
            if participant!= first_participant:
                for schedule in schedules:
                    if start_time < schedule[0] < end_time:
                        # If the time slot is not available, skip to the next time slot
                        break
                else:
                    # If the time slot is available for all participants, check if it meets the preferences
                    for preferred_time in preferences.get(participant, []):
                        if start_time >= preferred_time[0] and end_time <= preferred_time[1]:
                            # If the time slot meets the preferences, return the proposed meeting time
                            return current_date.strftime("%A"), f"{start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')}"

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