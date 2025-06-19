from datetime import datetime, timedelta

def find_meeting_time(cheryl_schedule, kyle_schedule, duration, day):
    # Define the start and end of the work hours
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')

    # Initialize the meeting time to None
    meeting_time = None

    # Iterate over the possible start times for the meeting
    for hour in range(start_time.hour, end_time.hour):
        for minute in range(0, 60):
            # Create a datetime object for the current time
            current_time = datetime.combine(day, datetime.strptime(f'{hour}:{minute}', '%H:%M').time())

            # Check if the current time is available for both participants
            if (current_time + timedelta(minutes=duration)).time() <= end_time.time() and \
               current_time.time() >= start_time.time() and \
               not is_busy(cheryl_schedule, current_time) and \
               not is_busy(kyle_schedule, current_time):
                # If the current time is available, update the meeting time
                meeting_time = (current_time, current_time + timedelta(minutes=duration))
                break

    # Return the meeting time in the required format
    if meeting_time:
        return f'{meeting_time[0].strftime("%H:%M")}-{meeting_time[1].strftime("%H:%M")}, {day.strftime("%A")}'
    else:
        return 'No available time found'

def is_busy(schedule, time):
    for start, end in schedule:
        if start <= time < end:
            return True
    return False

# Define the schedules for Cheryl and Kyle
cheryl_schedule = [
    (datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
    (datetime.strptime('11:30', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
    (datetime.strptime('15:30', '%H:%M'), datetime.strptime('16:00', '%H:%M')),
    (datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M'))  # Added this line
]

kyle_schedule = [
    (datetime.strptime('09:00', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
    (datetime.strptime('09:30', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
    (datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
    (datetime.strptime('10:00', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
    (datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
    (datetime.strptime('14:30', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
]

# Find a meeting time that works for both participants
day = datetime.strptime('2024-07-29', '%Y-%m-%d').date()  # Monday
duration = 30  # 30 minutes
print(find_meeting_time(cheryl_schedule, kyle_schedule, duration, day))