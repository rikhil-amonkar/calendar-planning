from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, meeting_duration, schedules):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
        start_time (str): Start time of the day in 'HH:MM' format.
        end_time (str): End time of the day in 'HH:MM' format.
        meeting_duration (int): Duration of the meeting in minutes.
        schedules (dict): Schedules of each participant.

    Returns:
        str: Proposed time in 'HH:MM:HH:MM' format and the day of the week.
    """

    # Convert start and end times to datetime objects
    start_time = datetime.strptime(start_time, '%H:%M')
    end_time = datetime.strptime(end_time, '%H:%M')

    # Initialize proposed time
    proposed_time = start_time

    # Loop until we find a time that works for everyone
    while proposed_time < end_time:
        # Check if the proposed time works for everyone
        works_for_everyone = True
        for participant, schedule in schedules.items():
            # Check if the proposed time conflicts with any of the participant's meetings
            for meeting in schedule:
                if proposed_time >= meeting[0] and proposed_time < meeting[1]:
                    works_for_everyone = False
                    break

        # If the proposed time works for everyone, return it
        if works_for_everyone:
            # Calculate the end time of the meeting
            meeting_end_time = proposed_time + timedelta(minutes=meeting_duration)

            # Return the proposed time and the day of the week
            return f"{proposed_time.strftime('%H:%M')}:{meeting_end_time.strftime('%H:%M')} on {proposed_time.strftime('%A')}"

        # If the proposed time doesn't work for everyone, move to the next time slot
        proposed_time += timedelta(minutes=30)

    # If no time works for everyone, return a message
    return "No time works for everyone's schedule and constraints."


# Example usage
schedules = {
    'Danielle': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('10:00', '%H:%M')),
                 (datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
                 (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
                 (datetime.strptime('15:30', '%H:%M'), datetime.strptime('16:00', '%H:%M')),
                 (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Bruce': [(datetime.strptime('11:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
              (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
              (datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
              (datetime.strptime('15:30', '%H:%M'), datetime.strptime('16:00', '%H:%M'))],
    'Eric': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
             (datetime.strptime('10:00', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
             (datetime.strptime('11:30', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
             (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:30', '%H:%M'))]
}

print(find_meeting_time('09:00', '17:00', 60, schedules))