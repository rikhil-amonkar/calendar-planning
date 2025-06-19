from datetime import datetime, timedelta

def find_meeting_time(available_days, start_time, end_time, meeting_duration):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
        available_days (list): List of available days of the week (Monday, Tuesday, Wednesday).
        start_time (dict): Existing schedule for each participant.
        end_time (dict): Existing schedule for each participant.
        meeting_duration (int): Duration of the meeting in minutes.

    Returns:
        tuple: Proposed meeting time and day of the week.
    """

    # Iterate over each available day
    for day in available_days:
        # Get the start and end times for the current day
        day_start = datetime.strptime(f"{day} 09:00:00", "%A %H:%M:%S")
        day_end = datetime.strptime(f"{day} 17:00:00", "%A %H:%M:%S")

        # Iterate over each participant's schedule
        for participant in start_time:
            # Get the participant's start and end times for the current day
            participant_start = start_time[participant]
            participant_end = end_time[participant]

            # Convert the participant's start and end times to datetime objects
            participant_start = [datetime.strptime(time, "%H:%M") for time in participant_start]
            participant_end = [datetime.strptime(time, "%H:%M") for time in participant_end]

            # Iterate over each time slot in the participant's schedule
            for i in range(len(participant_start)):
                # Get the current time slot
                current_start = participant_start[i]
                current_end = participant_end[i]

                # Check if the meeting can be scheduled in the current time slot
                if current_start >= day_start and current_end <= day_end:
                    # Calculate the available time in the current time slot
                    available_time = (current_start - day_start).total_seconds() / 3600
                    available_time += (day_end - current_end).total_seconds() / 3600

                    # Check if the available time is sufficient for the meeting
                    if available_time >= meeting_duration / 60:
                        # Calculate the start and end times for the meeting
                        meeting_start = day_start + timedelta(hours=available_time - meeting_duration / 60)
                        meeting_end = day_start + timedelta(hours=available_time)

                        # Return the proposed meeting time and day
                        return f"{meeting_start.strftime('%H:%M')}-{meeting_end.strftime('%H:%M')} {day}"

    # If no suitable time is found, return a message
    return "No suitable time found"

# Define the existing schedules for each participant
start_time = {
    "Patrick": [],
    "Roy": [
        ["10:00", "11:30"],
        ["12:00", "13:00"],
        ["14:00", "14:30"],
        ["15:00", "17:00"],
        ["10:30", "11:30"],
        ["12:00", "14:30"],
        ["15:00", "15:30"],
        ["16:00", "17:00"],
        ["09:30", "11:30"],
        ["12:30", "14:00"],
        ["14:30", "15:30"],
        ["16:30", "17:00"]
    ]
}

end_time = {
    "Patrick": [],
    "Roy": [
        ["11:30", "12:00"],
        ["13:00", "14:00"],
        ["14:30", "15:00"],
        ["17:00", "18:00"],
        ["11:30", "12:00"],
        ["14:30", "15:00"],
        ["15:30", "16:00"],
        ["17:00", "18:00"],
        ["11:30", "12:30"],
        ["14:00", "14:30"],
        ["15:30", "16:30"],
        ["17:00", "18:00"]
    ]
}

# Define the meeting duration and available days
meeting_duration = 60
available_days = ["Monday", "Tuesday", "Wednesday"]

# Find a suitable time for the meeting
proposed_time = find_meeting_time(available_days, start_time, end_time, meeting_duration)

# Print the proposed meeting time and day
print(proposed_time)