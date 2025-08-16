from datetime import datetime, timedelta

def can_schedule_meeting(current_time, meeting_start, meeting_end, min_duration):
    """
    Check if a meeting can be scheduled starting from `meeting_start` until `meeting_end`
    with a minimum duration of `min_duration`.

    :param current_time: The current time as a datetime object.
    :param meeting_start: The proposed start time for the meeting as a datetime object.
    :param meeting_end: The proposed end time for the meeting as a datetime object.
    :param min_duration: The minimum duration of the meeting as a timedelta object.
    :return: True if the meeting can be scheduled, False otherwise.
    """
    # Check if the current time is before or equal to the meeting start time
    # and if the difference between meeting end and meeting start is at least the minimum duration
    return (current_time <= meeting_start) and ((meeting_end - meeting_start) >= min_duration)

# Example usage:
current_time = datetime(2025, 7, 22, 16, 0)  # Current time is 4 PM
meeting_start = datetime(2025, 7, 22, 17, 0)  # Meeting starts at 5 PM
meeting_end = datetime(2025, 7, 22, 19, 0)  # Meeting ends at 7 PM
min_duration = timedelta(hours=1)  # Minimum duration is 1 hour

print(can_schedule_meeting(current_time, meeting_start, meeting_end, min_duration))  # Should print True