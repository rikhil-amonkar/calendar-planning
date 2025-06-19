from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, meeting_duration, schedules):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
    start_time (str): Start time of the work hours (e.g., 9:00).
    end_time (str): End time of the work hours (e.g., 17:00).
    meeting_duration (int): Duration of the meeting in minutes (e.g., 30).
    schedules (dict): Dictionary of participants' schedules.

    Returns:
    str: Proposed time range in the format HH:MM-HH:MM and the day of the week.
    """
    # Convert start and end times to datetime objects
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")

    # Find the first available time slot
    for hour in range(start_time.hour, end_time.hour):
        for minute in range(0, 60, meeting_duration):
            time = datetime.combine(datetime.today().date(), datetime.min.time().replace(hour=hour, minute=minute))
            if is_available(time, time + timedelta(minutes=meeting_duration), schedules):
                return f"{time.strftime('%H:%M')}-{(time + timedelta(minutes=meeting_duration)).strftime('%H:%M')} {time.strftime('%A')}"

    # If no available time slot is found, return a message
    return "No available time slot found."

def is_available(time, end_time, schedules):
    """
    Check if a time slot is available for all participants.

    Args:
    time (datetime): Start time of the time slot.
    end_time (datetime): End time of the time slot.
    schedules (dict): Dictionary of participants' schedules.

    Returns:
    bool: True if the time slot is available for all participants, False otherwise.
    """
    for participant, schedule in schedules.items():
        for block in schedule:
            if (block[0] <= end_time and block[1] >= time):
                return False
    return True

# Define participants' schedules
schedules = {
    "Joe": [(datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:00', '%H:%M'))],
    "Keith": [(datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M'))],
    "Patricia": [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M'))],
    "Nancy": [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('11:00', '%H:%M'))],
    "Pamela": [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('10:00', '%H:%M')),
               (datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
               (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:30', '%H:%M')),
               (datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
               (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
               (datetime.strptime('15:30', '%H:%M'), datetime.strptime('16:00', '%H:%M')),
               (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))]
}

# Define meeting duration and work hours
meeting_duration = 30
start_time = "9:00"
end_time = "17:00"

# Find a time that works for everyone's schedule and constraints
proposed_time = find_meeting_time(start_time, end_time, meeting_duration, schedules)

# Print the proposed time and day of the week
print(proposed_time)