from datetime import datetime, timedelta

def find_available_time(start_time, end_time, schedule):
    """
    Find a time slot within the given schedule that is available.
    
    Args:
    start_time (datetime): The start time of the meeting.
    end_time (datetime): The end time of the meeting.
    schedule (list): A list of time slots that are blocked.
    
    Returns:
    tuple: A tuple containing the available start time and end time.
    """
    available_time = None
    for time_slot in schedule:
        if time_slot[0] >= start_time and time_slot[1] <= end_time:
            return None
        elif time_slot[0] > end_time:
            available_time = (start_time, time_slot[0])
            break
        elif time_slot[1] < start_time:
            available_time = (time_slot[1], end_time)
            break
    if available_time is None:
        available_time = (start_time, end_time)
    return available_time

def find_meeting_time(days, meeting_duration, schedule):
    """
    Find a time that works for everyone's schedule and constraints.
    
    Args:
    days (list): A list of days to consider.
    meeting_duration (int): The duration of the meeting in minutes.
    schedule (dict): A dictionary containing the schedule for each person.
    
    Returns:
    tuple: A tuple containing the day of the week, start time, and end time of the meeting.
    """
    for day in days:
        start_time = datetime.strptime(f"{day}:09:00", "%A:%H:%M")
        end_time = datetime.strptime(f"{day}:17:00", "%A:%H:%M")
        while start_time < end_time:
            meeting_end_time = start_time + timedelta(minutes=meeting_duration)
            if all(find_available_time(start_time, meeting_end_time, schedule[person][day]) is not None for person in schedule):
                return day, start_time.strftime("%H:%M"), meeting_end_time.strftime("%H:%M")
            start_time += timedelta(minutes=30)
    return None

# Define the schedule for each person
schedule = {
    "Mary": {
        "Monday": [],
        "Tuesday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                    (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
        "Wednesday": [(datetime.strptime("9:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                      (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
        "Thursday": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                     (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M"))]
    },
    "Alexis": {
        "Monday": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                   (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                   (datetime.strptime("12:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
        "Tuesday": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                    (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                    (datetime.strptime("12:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                    (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
        "Wednesday": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                      (datetime.strptime("11:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
        "Thursday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                     (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                     (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                     (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
    }
}

# Define the meeting duration
meeting_duration = 30

# Define the days to consider
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

# Find a time that works for everyone's schedule and constraints
result = find_meeting_time(days, meeting_duration, schedule)

# Print the result
if result:
    day, start_time, end_time = result
    print(f"{day}: {start_time} - {end_time}")
else:
    print("No available time found")