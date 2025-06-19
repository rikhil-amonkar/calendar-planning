from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, meeting_duration, schedules, preferences):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
    start_time (datetime): The start of the workday.
    end_time (datetime): The end of the workday.
    meeting_duration (timedelta): The duration of the meeting.
    schedules (dict): A dictionary of participant schedules.
    preferences (dict): A dictionary of participant preferences.

    Returns:
    tuple: A tuple containing the proposed meeting time and day of the week.
    """
    # Create a list to store possible meeting times
    possible_meeting_times = []

    # Iterate over the workday in 30-minute increments
    for hour in range(start_time.hour, end_time.hour):
        for minute in range(0, 60, 30):
            # Create a datetime object for the current time
            time = start_time.replace(hour=hour, minute=minute)

            # Check if the time is available for all participants
            is_available = True
            for participant, schedule in schedules.items():
                # Check if the time conflicts with any of the participant's scheduled meetings
                for start, end in schedule:
                    if start <= time + meeting_duration <= end:
                        is_available = False
                        break
                if not is_available:
                    break

            # If the time is available, add it to the list of possible meeting times
            if is_available:
                possible_meeting_times.append((time, time + meeting_duration))

    # Filter the possible meeting times based on the participant's preferences
    if 'avoid_after' in preferences.get('Jack', {}):
        possible_meeting_times = [time for time in possible_meeting_times if time[0].hour < preferences['Jack'].get('avoid_after', 17)]

    # Return the first possible meeting time
    return possible_meeting_times[0] if possible_meeting_times else None


def main():
    # Define the start and end of the workday
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')

    # Define the meeting duration
    meeting_duration = timedelta(hours=0, minutes=30)

    # Define the schedules for each participant
    schedules = {
        'Jack': [
            (datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
            (datetime.strptime('11:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
            (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
            (datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
            (datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M')),
        ],
        'Charlotte': [
            (datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:00', '%H:%M')),
            (datetime.strptime('10:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
            (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
            (datetime.strptime('14:00', '%H:%M'), datetime.strptime('16:00', '%H:%M')),
        ],
    }

    # Define the participant's preferences
    preferences = {
        'Jack': {
            'avoid_after': 12.5,
        },
    }

    # Find a suitable meeting time
    meeting_time = find_meeting_time(start_time, end_time, meeting_duration, schedules, preferences)

    # If a meeting time was found, print it
    if meeting_time:
        print(f"Meeting time: {meeting_time[0].strftime('%H:%M')} - {meeting_time[1].strftime('%H:%M')}")
        print(f"Day of the week: {meeting_time[0].weekday()}")
    else:
        print("No suitable meeting time found.")


if __name__ == "__main__":
    main()