from datetime import datetime, timedelta

def schedule_meeting(start_time, end_time, meeting_duration, busy_schedules):
    """
    Schedule a meeting between two people given their busy schedules.

    Args:
    start_time (datetime): The start of the workday.
    end_time (datetime): The end of the workday.
    meeting_duration (int): The duration of the meeting in minutes.
    busy_schedules (dict): A dictionary with participant names as keys and their busy schedules as values.

    Returns:
    tuple: A tuple containing the proposed meeting time and day.
    """
    # Convert the busy schedules to a list of tuples
    busy_schedules_list = []
    for name, schedule in busy_schedules.items():
        busy_schedules_list.append((name, schedule))

    # Calculate the end time of the meeting
    meeting_end_time = start_time + timedelta(minutes=meeting_duration)

    # Initialize the proposed meeting time
    proposed_meeting_time = None

    # Iterate over the available time slots
    for hour in range(start_time.hour, end_time.hour):
        for minute in range(0, 60, 30):
            # Calculate the start and end times of the current time slot
            time_slot_start = start_time.replace(hour=hour, minute=minute)
            time_slot_end = time_slot_start + timedelta(minutes=30)

            # Check if the current time slot is available for all participants
            if all(time_slot_start >= schedule[0] and time_slot_end <= schedule[1] for _, schedule in busy_schedules_list):
                # Check if the meeting can be scheduled within the current time slot
                if time_slot_start + timedelta(minutes=meeting_duration) <= time_slot_end:
                    # Update the proposed meeting time
                    proposed_meeting_time = (time_slot_start, time_slot_start + timedelta(minutes=meeting_duration))
                    break
        if proposed_meeting_time:
            break

    # Return the proposed meeting time and day
    if proposed_meeting_time:
        return proposed_meeting_time, start_time.strftime('%A')
    else:
        return None, None


# Example usage:
start_time = datetime.strptime('09:00', '%H:%M')
end_time = datetime.strptime('17:00', '%H:%M')
meeting_duration = 30
busy_schedules = {
    'Lisa': (datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
    'Lisa': (datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
    'Lisa': (datetime.strptime('14:00', '%H:%M'), datetime.strptime('16:00', '%H:%M')),
    'Anthony': (datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
    'Anthony': (datetime.strptime('11:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
    'Anthony': (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
    'Anthony': (datetime.strptime('14:00', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
    'Anthony': (datetime.strptime('15:30', '%H:%M'), datetime.strptime('16:00', '%H:%M')),
    'Anthony': (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
}

proposed_meeting_time, day = schedule_meeting(start_time, end_time, meeting_duration, busy_schedules)

if proposed_meeting_time:
    print(f"{proposed_meeting_time[0].strftime('%H:%M')} - {proposed_meeting_time[1].strftime('%H:%M')} on {day}")
else:
    print("No available time slot found.")