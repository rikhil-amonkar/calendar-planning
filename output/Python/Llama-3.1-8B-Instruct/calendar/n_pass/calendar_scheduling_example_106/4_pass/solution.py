from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, meeting_duration, schedules):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
        start_time (str): Start time of the day (e.g., 09:00).
        end_time (str): End time of the day (e.g., 17:00).
        meeting_duration (int): Duration of the meeting in minutes.
        schedules (dict): Dictionary of schedules where each key is a participant's name
            and each value is a list of tuples representing their blocked time slots.

    Returns:
        str: Proposed time range in the format HH:MM-HH:MM, day of the week.
    """
    # Convert time strings to datetime objects
    start_time = datetime.strptime(start_time, '%H:%M')
    end_time = datetime.strptime(end_time, '%H:%M')

    # Calculate the end time of the meeting
    meeting_end_time = start_time + timedelta(minutes=meeting_duration)

    # Check if the meeting can be scheduled within the work hours
    if meeting_end_time > end_time:
        return None

    # Iterate over all possible meeting start times
    for hour in range(start_time.hour, end_time.hour):
        for minute in range(0, 60):
            meeting_start_time = datetime(start_time.year, start_time.month, start_time.day, hour, minute)

            # Check if the meeting time slot is available for all participants
            if all(
                not any(
                    (meeting_start_time >= datetime.strptime(f"{start_time_block[0]:02d}:{start_time_block[1]:02d}", '%H:%M') and
                     meeting_start_time < datetime.strptime(f"{start_time_block[0]+1:02d}:00", '%H:%M'))
                    or (meeting_end_time > datetime.strptime(f"{start_time_block[0]:02d}:{start_time_block[1]:02d}", '%H:%M') and
                        meeting_end_time <= datetime.strptime(f"{start_time_block[0]+1:02d}:00", '%H:%M'))
                    for start_time_block in schedule
                )
                for schedule in schedules.values()
            ):
                return f"{meeting_start_time.strftime('%H:%M')}-{meeting_end_time.strftime('%H:%M')}, {start_time.strftime('%A')}"

    # If no suitable time slot is found, return None
    return None


# Example usage
schedules = {
    'Olivia': [(12, 30), (14, 30), (16, 30)],
    'Anna': [],
    'Virginia': [(9, 0), (11, 30), (16, 0), (16, 30)],
    'Paul': [(9, 0), (11, 0), (13, 0), (14, 30), (16, 0), (16, 30)]
}

start_time = '09:00'
end_time = '17:00'
meeting_duration = 60  # 1 hour

result = find_meeting_time(start_time, end_time, meeting_duration, schedules)

if result:
    print(f"Proposed time: {result}")
else:
    print("No suitable time slot found.")