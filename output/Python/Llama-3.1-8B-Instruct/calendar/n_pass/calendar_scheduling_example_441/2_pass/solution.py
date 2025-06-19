from datetime import datetime, timedelta

def find_available_time(start_time, end_time, schedules):
    """
    Find all available time slots between start_time and end_time.
    
    Args:
        start_time (datetime): The start time of the day.
        end_time (datetime): The end time of the day.
        schedules (list of tuples): A list of tuples, where each tuple contains two datetime objects representing the start and end time of a schedule.
    
    Returns:
        list of datetime: A list of datetime objects representing the available time slots.
    """
    available_time = []
    for time in [start_time + timedelta(minutes=i) for i in range((end_time - start_time).seconds // 60 + 1)]:
        is_available = True
        for schedule in schedules:
            if schedule[0] <= time < schedule[1]:
                is_available = False
                break
        if is_available:
            available_time.append(time)
    return available_time

def find_meeting_time(schedules, duration):
    """
    Find the first available time slot that is at least duration minutes long.
    
    Args:
        schedules (list of lists of tuples): A list of lists of tuples, where each tuple contains two datetime objects representing the start and end time of a schedule.
        duration (int): The minimum duration of the meeting in minutes.
    
    Returns:
        tuple of str: A tuple of two strings representing the start and end time of the meeting, or None if no available time slot is found.
    """
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')
    available_times = find_available_time(start_time, end_time, [schedule for schedules in schedules for schedule in schedules])
    for time in available_times:
        if (time + timedelta(minutes=duration)).time() <= end_time.time():
            return time.strftime('%H:%M'), (time + timedelta(minutes=duration)).strftime('%H:%M')
    return None

def main():
    schedules = [
        [(datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M'))],
        [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('10:00', '%H:%M'))],
        [(datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M'))],
        [(datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))],
        [(datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:00', '%H:%M'))],
        [(datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M'))],
        [(datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:00', '%H:%M'))],
        [(datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))],
        [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('11:00', '%H:%M'))],
        [(datetime.strptime('12:00', '%H:%M'), datetime.strptime('13:00', '%H:%M'))],
        [(datetime.strptime('14:00', '%H:%M'), datetime.strptime('15:00', '%H:%M'))],
        [(datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:00', '%H:%M'))],
        [(datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:30', '%H:%M'))],
        [(datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:00', '%H:%M'))],
        [(datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M'))],
        [(datetime.strptime('16:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
        [(datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:00', '%H:%M'))],
        [(datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M'))],
        [(datetime.strptime('11:30', '%H:%M'), datetime.strptime('13:00', '%H:%M'))],
        [(datetime.strptime('14:00', '%H:%M'), datetime.strptime('16:00', '%H:%M'))],
        [(datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))]
    ]
    duration = 30
    meeting_time = find_meeting_time(schedules, duration)
    if meeting_time:
        day_of_week = datetime.strptime('2024-07-29', '%Y-%m-%d').strftime('%A')
        print(f"Day of week: {day_of_week}")
        print(f"Meeting time: {meeting_time[0]} - {meeting_time[1]}")
    else:
        print("No available time found.")

if __name__ == "__main__":
    main()