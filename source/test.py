def find_meeting_time(participants, meeting_duration, start_time, end_time):
    """
    Find a meeting time that works for everyone's schedule.

    Args:
        participants (dict): Dictionary of participants with their existing schedules.
        meeting_duration (int): Duration of the meeting in minutes.
        start_time (int): Start time of the workday in minutes (e.g., 9:00 = 540).
        end_time (int): End time of the workday in minutes (e.g., 17:00 = 1020).

    Returns:
        tuple: Proposed meeting time as a tuple of start and end times.
    """

    # Convert time to minutes
    def time_to_minutes(time):
        hours, minutes = map(int, time.split(':'))
        return hours * 60 + minutes

    # Convert minutes to time
    def minutes_to_time(minutes):
        hours, minutes = divmod(minutes, 60)
        return f"{hours:02d}:{minutes:02d}"

    # Initialize the proposed meeting time
    proposed_time = None

    # Iterate over the possible meeting times
    for time in range(start_time, end_time - meeting_duration + 1):
        # Assume the current time works for everyone
        works_for_everyone = True

        # Check if the current time works for each participant
        for participant, schedule in participants.items():
            for start, end in schedule:
                # Convert schedule times to minutes
                start_minutes = time_to_minutes(start)
                end_minutes = time_to_minutes(end)

                # If the current time overlaps with a scheduled meeting, it doesn't work
                if start_minutes <= time < end_minutes or start_minutes < time + meeting_duration <= end_minutes:
                    works_for_everyone = False
                    break

            # If the current time doesn't work for this participant, move on to the next time
            if not works_for_everyone:
                break

        # If the current time works for everyone, propose it
        if works_for_everyone:
            proposed_time = (minutes_to_time(time), minutes_to_time(time + meeting_duration))
            break

    return proposed_time


# Define the existing schedules for each participant
participants = {
    "Michelle": [("11:00", "12:00")],
    "Steven": [("9:00", "9:30"), ("11:30", "12:00"), ("13:30", "14:00"), ("15:30", "16:00")],
    "Jerry": [("9:00", "9:30"), ("10:00", "11:00"), ("11:30", "12:30"), ("13:00", "14:30"), ("15:30", "16:00"), ("16:30", "17:00")]
}

# Define the meeting duration and work hours
meeting_duration = 60  # 1 hour
start_time = time_to_minutes("9:00")  # 540
end_time = time_to_minutes("17:00")  # 1020

# Find the proposed meeting time
proposed_time = find_meeting_time(participants, meeting_duration, start_time, end_time)

# Print the proposed meeting time
print("Proposed meeting time:", proposed_time)