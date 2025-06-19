from datetime import datetime, timedelta

def find_meeting_time(judith_schedule, timothy_schedule, meeting_duration, preferred_days=None, judith_preferences=None, timothy_preferences=None):
    """
    Find a suitable time for a meeting between Judith and Timothy based on their schedules and constraints.

    Args:
        judith_schedule (dict): Judith's schedule with blocked times.
        timothy_schedule (dict): Timothy's schedule with blocked times.
        meeting_duration (int): The duration of the meeting in minutes.
        preferred_days (list, optional): The days of the week to consider for the meeting. Defaults to None.
        judith_preferences (dict, optional): Judith's preferences for the meeting time. Defaults to None.
        timothy_preferences (dict, optional): Timothy's preferences for the meeting time. Defaults to None.

    Returns:
        tuple: A tuple containing the proposed meeting time and day, or (None, None) if no suitable time is found.
    """

    # Define the days of the week
    days = ['Monday', 'Tuesday', 'Wednesday']

    # If no preferred days are specified, consider all days
    if preferred_days is None:
        preferred_days = days

    # Initialize the meeting time and day
    meeting_time = None
    meeting_day = None

    # Iterate over the preferred days
    for day in preferred_days:
        # Get Judith's schedule for the current day
        judith_day_schedule = judith_schedule.get(day, [])

        # Get Timothy's schedule for the current day
        timothy_day_schedule = timothy_schedule.get(day, [])

        # Sort the time slots in Judith's schedule for the current day
        judith_day_schedule.sort(key=lambda x: x[0])

        # Sort the time slots in Timothy's schedule for the current day
        timothy_day_schedule.sort(key=lambda x: x[0])

        # Iterate over the time slots in Judith's schedule for the current day
        for judith_time in judith_day_schedule:
            # Iterate over the time slots in Timothy's schedule for the current day
            for timothy_time in timothy_day_schedule:
                # Check if the meeting time does not conflict with either Judith's or Timothy's schedule
                if (judith_time[0] < timothy_time[0] and judith_time[1] > timothy_time[0]) or (timothy_time[0] < judith_time[0] and timothy_time[1] > judith_time[0]):
                    # Check if the time slots do not overlap
                    if judith_time[1] > timothy_time[0] and judith_time[0] < timothy_time[1]:
                        continue

                    # Check if the meeting time meets Judith's preferences
                    if judith_preferences is None or (judith_time[0] >= judith_preferences['start'] and judith_time[0] <= judith_preferences['end']):
                        # Check if the meeting time meets Timothy's preferences
                        if timothy_preferences is None or (timothy_time[0] >= timothy_preferences['start'] and timothy_time[0] <= timothy_preferences['end']):
                            # Calculate the available time slot
                            available_time = max(judith_time[0], timothy_time[0])
                            end_time = min(judith_time[1], timothy_time[1])

                            # Check if the available time slot is long enough for the meeting
                            if available_time + meeting_duration <= end_time:
                                # Check if the available time slot is within the valid time range
                                if 9 <= available_time.hour < 17 and 9 <= end_time.hour < 17:
                                    # Update the meeting time and day
                                    meeting_time = (available_time, available_time + timedelta(minutes=meeting_duration))
                                    meeting_day = day

                                    # Break out of the inner loops
                                    break
            if meeting_time is not None:
                break
        if meeting_time is not None:
            break

    # Return the proposed meeting time and day, or (None, None) if no suitable time is found
    if meeting_time is None:
        return None, None
    else:
        return (meeting_time[0].strftime('%H:%M'), meeting_time[1].strftime('%H:%M')), meeting_day


# Example usage:
judith_schedule = {
    'Monday': [(9, 17), (12, 12.5)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(11.5, 12), (9, 17)]
}

timothy_schedule = {
    'Monday': [(9.5, 10), (10.5, 11.5), (12.5, 14), (15.5, 17)],
    'Tuesday': [(9.5, 13), (13.5, 14), (14.5, 17)],
    'Wednesday': [(9, 9.5), (10.5, 11), (13.5, 14.5), (15, 15.5), (16, 16.5)]
}

meeting_duration = 60  # 1 hour

preferred_days = ['Monday', 'Tuesday', 'Wednesday']

judith_preferences = {
   'start': 12,
    'end': 16
}

timothy_preferences = {
   'start': 10,
    'end': 15
}

meeting_time, meeting_day = find_meeting_time(judith_schedule, timothy_schedule, meeting_duration, preferred_days, judith_preferences, timothy_preferences)

if meeting_time is not None:
    print(f"Proposed meeting time: {meeting_time[0]}-{meeting_time[1]} on {meeting_day}")
else:
    print("No suitable meeting time found.")