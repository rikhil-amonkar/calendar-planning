from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, meeting_duration, participant_schedules):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
    start_time (datetime): Start time of the work hours.
    end_time (datetime): End time of the work hours.
    meeting_duration (int): Duration of the meeting in minutes.
    participant_schedules (dict): Dictionary of participant's schedules.

    Returns:
    tuple: A proposed time in the format HH:MM:HH:MM and the day of the week.
    """
    # Initialize the proposed time to the start of the work hours
    proposed_time = start_time

    # Loop through the work hours until we find a time that works for everyone
    while proposed_time < end_time:
        # Check if the proposed time works for everyone
        if all(not (start_time <= proposed_time < schedule[0] or 
                    schedule[1] < proposed_time + timedelta(minutes=meeting_duration) <= end_time) 
               for schedule in participant_schedules.values()):
            # Check if the proposed time conflicts with the unavailable time slot
            if not (datetime(2024, 7, 29, 17, 0) <= proposed_time < datetime(2024, 7, 29, 24, 0) or 
                    datetime(2024, 7, 29, 17, 0) <= proposed_time + timedelta(minutes=meeting_duration) < datetime(2024, 7, 29, 24, 0)):
                # If it does not conflict, return the proposed time and the day of the week
                return f"{proposed_time.strftime('%H:%M')}:{(proposed_time + timedelta(minutes=meeting_duration)).strftime('%H:%M')}", proposed_time.strftime('%A')

        # If it doesn't, move on to the next time slot
        proposed_time += timedelta(minutes=30)

    # If we've reached the end of the work hours and haven't found a time that works, return a message
    return "No available time found", None


# Define the participant's schedules
kayla_schedule = {'Kayla': (datetime(2024, 7, 29, 10, 0), datetime(2024, 7, 29, 10, 30)) + 
                     (datetime(2024, 7, 29, 14, 30), datetime(2024, 7, 29, 16, 0))}
rebecca_schedule = {'Rebecca': (datetime(2024, 7, 29, 9, 0), datetime(2024, 7, 29, 13, 0)) + 
                    (datetime(2024, 7, 29, 13, 30), datetime(2024, 7, 29, 15, 0)) + 
                    (datetime(2024, 7, 29, 15, 30), datetime(2024, 7, 29, 16, 0))}

# Define the start and end times of the work hours
start_time = datetime(2024, 7, 29, 9, 0)
end_time = datetime(2024, 7, 29, 17, 0)

# Define the meeting duration
meeting_duration = 60  # Adjusted the meeting duration to be 60 minutes

# Find a time that works for everyone
proposed_time, day_of_week = find_meeting_time(start_time, end_time, meeting_duration, {**kayla_schedule, **rebecca_schedule})

# Print the proposed time and the day of the week
print(f"Proposed time: {proposed_time} on {day_of_week}")