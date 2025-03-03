from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_hours):
    """
    Find a suitable time slot for a meeting given the existing schedules of all participants.

    Args:
        participants (dict): A dictionary where the keys are the names of the participants and the values are lists of tuples representing the start and end times of their existing meetings.
        meeting_duration (int): The duration of the meeting in minutes.
        work_hours (tuple): A tuple representing the start and end times of the work hours.

    Returns:
        tuple: A tuple representing the start and end times of the proposed meeting.
    """

    # Convert the work hours to datetime objects
    work_start = datetime.strptime(work_hours[0], '%H:%M')
    work_end = datetime.strptime(work_hours[1], '%H:%M')

    # Initialize the proposed meeting time to the start of the work hours
    proposed_start = work_start

    # Loop until we find a suitable time slot
    while proposed_start < work_end:
        # Calculate the end time of the proposed meeting
        proposed_end = proposed_start + timedelta(minutes=meeting_duration)

        # Check if the proposed meeting time conflicts with any of the participants' existing meetings
        conflict = False
        for participant, meetings in participants.items():
            for start, end in meetings:
                start_time = datetime.strptime(start, '%H:%M')
                end_time = datetime.strptime(end, '%H:%M')
                if (proposed_start >= start_time and proposed_start < end_time) or (proposed_end > start_time and proposed_end <= end_time):
                    conflict = True
                    break
            if conflict:
                break

        # If there is no conflict, return the proposed meeting time
        if not conflict:
            return (proposed_start.strftime('%H:%M'), proposed_end.strftime('%H:%M'))

        # If there is a conflict, increment the proposed start time by 30 minutes
        proposed_start += timedelta(minutes=30)

    # If we cannot find a suitable time slot, return None
    return None


# Example usage
participants = {
    'Michelle': [('11:00', '12:00')],
    'Steven': [('9:00', '9:30'), ('11:30', '12:00'), ('13:30', '14:00'), ('15:30', '16:00')],
    'Jerry': [('9:00', '9:30'), ('10:00', '11:00'), ('11:30', '12:30'), ('13:00', '14:30'), ('15:30', '16:00'), ('16:30', '17:00')]
}
meeting_duration = 60
work_hours = ('9:00', '17:00')

proposed_time = find_meeting_time(participants, meeting_duration, work_hours)
if proposed_time:
    print('Proposed meeting time:', proposed_time[0], '-', proposed_time[1])
else:
    print('No suitable time slot found.')
    