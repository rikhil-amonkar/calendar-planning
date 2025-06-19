from datetime import datetime, timedelta

def find_available_time(start_time, end_time, busy_times):
    """
    Find the first available time slot within the given time range.
    
    Args:
    start_time (datetime): The start of the time range.
    end_time (datetime): The end of the time range.
    busy_times (list): A list of busy time slots.
    
    Returns:
    tuple: The start and end times of the available time slot.
    """
    available_time = None
    for time in [start_time + timedelta(minutes=i) for i in range((end_time - start_time).seconds // 60 + 1)]:
        if not any((time - timedelta(minutes=i)).time() <= busy_time.time() <= time.time() for i, busy_time in enumerate(busy_times) if busy_time.time() < end_time.time()):
            available_time = (time, time + timedelta(minutes=30))
            break
    return available_time

def schedule_meeting(day, start_time, end_time, busy_times):
    """
    Schedule a meeting based on the given constraints.
    
    Args:
    day (str): The day of the week.
    start_time (datetime): The start of the work hours.
    end_time (datetime): The end of the work hours.
    busy_times (list): A list of busy time slots for each participant.
    
    Returns:
    tuple: The start and end times of the meeting.
    """
    meeting_start = None
    for time in [start_time + timedelta(minutes=i) for i in range((end_time - start_time).seconds // 60 + 1)]:
        available_time = find_available_time(time, end_time, busy_times)
        if available_time:
            meeting_start = available_time
            break
    return meeting_start

def main():
    # Define the work hours
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')
    
    # Define the busy times for each participant
    adam_busy_times = [datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:00', '%H:%M'), 
                       datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:00', '%H:%M'), 
                       datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:00', '%H:%M'), 
                       datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M')]
    roy_busy_times = [datetime.strptime('10:00', '%H:%M'), datetime.strptime('11:00', '%H:%M'), 
                      datetime.strptime('11:30', '%H:%M'), datetime.strptime('13:00', '%H:%M'), 
                      datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:30', '%H:%M'), 
                      datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M')]
    
    # Schedule the meeting
    day = 'Monday'
    meeting_start = schedule_meeting(day, start_time, end_time, adam_busy_times + roy_busy_times)
    
    # Print the result
    if meeting_start:
        print(f'The meeting will be held on {day} from {meeting_start[0].strftime("%H:%M")} to {meeting_start[1].strftime("%H:%M")}.')
    else:
        print('No available time slot found.')

if __name__ == '__main__':
    main()