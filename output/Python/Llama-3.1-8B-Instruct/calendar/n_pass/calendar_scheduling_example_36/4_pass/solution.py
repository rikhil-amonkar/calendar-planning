from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, meeting_duration, schedules):
    """
    Find a time slot that works for all participants.

    Args:
        start_time (datetime): Start of the workday.
        end_time (datetime): End of the workday.
        meeting_duration (timedelta): Duration of the meeting.
        schedules (dict): Dictionary of participant schedules.

    Returns:
        tuple: Proposed time slot and day of the week.
    """
    # Iterate over each hour in the workday
    for hour in range(int ((end_time - start_time).total_seconds() / 3600) + 1):
        time = start_time + timedelta(hours=hour)
        # Check if the time slot is available for all participants
        available = True
        for start, end in schedules.values():
            # Check if the time slot conflicts with any scheduled time
            if not (start <= time < end or start < time + meeting_duration <= end):
                available = False
                break
        if available:
            # Check if the time slot is after 12:30 for Denise
            if time + meeting_duration > datetime.strptime('12:30', '%H:%M').replace(year=start_time.year, month=start_time.month, day=start_time.day):
                return time.strftime('%H:%M'), (time + meeting_duration).strftime('%H:%M'), time.strftime('%A')

    # If no time slot is found, return a message
    return "No available time slot found."

# Define the existing schedules
schedules = {
    'Ryan': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')), 
             (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:00', '%H:%M'))],
    'Ruth': [],
    'Denise': [(datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:30', '%H:%M')), 
               (datetime.strptime('12:00', '%H:%M'), datetime.strptime('13:00', '%H:%M')), 
               (datetime.strptime('14:30', '%H:%M'), datetime.strptime('16:30', '%H:%M'))]
}

# Define the meeting duration
meeting_duration = timedelta(hours=1)

# Define the start and end times
start_time = datetime.strptime('09:00', '%H:%M').replace(year=datetime.now().year, month=datetime.now().month, day=datetime.now().weekday() + 1)
end_time = datetime.strptime('17:00', '%H:%M').replace(year=datetime.now().year, month=datetime.now().month, day=datetime.now().weekday() + 1)

# Find a time slot that works for all participants
proposed_time, end_time_str, day_of_week = find_meeting_time(start_time, end_time, meeting_duration, schedules)

# Print the proposed time slot and day of the week
print(f"{proposed_time}:{end_time_str} on {day_of_week}")