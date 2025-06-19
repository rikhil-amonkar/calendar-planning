from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, duration, schedules):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
        start_time (datetime): The start of the workday.
        end_time (datetime): The end of the workday.
        duration (timedelta): The duration of the meeting.
        schedules (dict): A dictionary of participant schedules.

    Returns:
        tuple: A tuple containing the start and end times of the meeting.
    """
    # Initialize the current time to the start of the workday
    current_time = start_time

    # Iterate over the participants
    for participant, times in schedules.items():
        # If the participant has no available time slots, skip them
        if not times:
            continue

        # Sort the participant's available time slots
        sorted_times = sorted(times, key=lambda x: x[0])

        # Iterate over the participant's available time slots
        for time in sorted_times:
            # Check if the current time is before the time slot
            if current_time < time[0]:
                # Check if the time slot has enough time for the meeting
                if time[0] + duration <= end_time:
                    # Return the meeting time
                    return current_time, current_time + duration

        # If no time slot is found, move to the next day
        current_time = end_time + timedelta(days=1)

    # If no time is found, return None
    return None

def main():
    # Define the start and end of the workday
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')

    # Define the duration of the meeting
    duration = timedelta(hours=0, minutes=30)

    # Define the schedules for each participant
    schedules = {
        'Megan': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
                  (datetime.strptime('10:00', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
                  (datetime.strptime('12:00', '%H:%M'), datetime.strptime('12:30', '%H:%M'))],
        'Christine': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
                      (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
                      (datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
                      (datetime.strptime('15:30', '%H:%M'), datetime.strptime('16:30', '%H:%M'))],
        'Gabriel': [],
        'Sara': [(datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
                 (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:00', '%H:%M'))],
        'Bruce': [(datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:00', '%H:%M')),
                  (datetime.strptime('10:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
                  (datetime.strptime('12:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
                  (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
                  (datetime.strptime('15:30', '%H:%M'), datetime.strptime('16:30', '%H:%M'))],
        'Kathryn': [(datetime.strptime('10:00', '%H:%M'), datetime.strptime('15:30', '%H:%M')),
                    (datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))],
        'Billy': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
                  (datetime.strptime('11:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
                  (datetime.strptime('12:00', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
                  (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:30', '%H:%M'))]
    }

    # Find the meeting time
    meeting_time = find_meeting_time(start_time, end_time, duration, schedules)

    # If a meeting time is found, print it
    if meeting_time:
        start_time_str = meeting_time[0].strftime('%H:%M')
        end_time_str = meeting_time[1].strftime('%H:%M')
        day_of_week = meeting_time[0].strftime('%A')
        print(f"Meeting time: {start_time_str} - {end_time_str} on {day_of_week}")
    else:
        print("No meeting time found.")

if __name__ == "__main__":
    main()