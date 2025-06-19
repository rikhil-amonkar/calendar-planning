from datetime import datetime, timedelta

def find_available_time(start_time, end_time, schedules, duration):
    """
    Find all available time slots within the given start and end time.

    Args:
    start_time (datetime): The start time.
    end_time (datetime): The end time.
    schedules (dict): A dictionary of schedules where each key is a person's name and each value is a tuple of time ranges.
    duration (int): The duration of the meeting.

    Returns:
    list: A list of available time slots.
    """
    available_time = []
    for time in [start_time + timedelta(minutes=i) for i in range((end_time - start_time).seconds // 60 + 1)]:
        # Check if the available time is not within any schedule
        conflicts = False
        for start, end in schedules.values():
            for start_range, end_range in zip([start] + [end] + list(schedules.values())[0], list(schedules.values())[0] + [end] + [start]):
                if (start_range <= time < end_range) or (start_range < time + timedelta(minutes=duration) <= end_range):
                    conflicts = True
                    break
            if conflicts:
                break
        else:
            available_time.append(time)
    return available_time

def schedule_meeting(start_time, end_time, schedules, duration):
    """
    Schedule a meeting within the given start and end time.

    Args:
    start_time (datetime): The start time.
    end_time (datetime): The end time.
    schedules (dict): A dictionary of schedules where each key is a person's name and each value is a tuple of time ranges.
    duration (int): The duration of the meeting.

    Returns:
    tuple: A tuple of start and end times of the scheduled meeting, or None if no available time is found.
    """
    available_times = find_available_time(start_time, end_time, schedules, duration)
    available_times.sort()
    for i in range(len(available_times) - duration):
        time_range = (available_times[i], available_times[i] + timedelta(minutes=duration))
        # Check if the available time plus the meeting duration is not within any schedule
        conflicts = False
        for start, end in schedules.values():
            for start_range, end_range in zip([start] + [end] + list(schedules.values())[0], list(schedules.values())[0] + [end] + [start]):
                if (start_range <= time_range[0] < end_range) or (start_range < time_range[1] <= end_range):
                    conflicts = True
                    break
            if conflicts:
                break
        else:
            return time_range

def main():
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')
    day_of_week = 'Monday'

    schedules = {
        'Andrea': (datetime.strptime('09:00', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
        'Jack': (datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')) + (datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
        'Madison': (datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:30', '%H:%M')) + (datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:00', '%H:%M')) + (datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M')) + (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
        'Rachel': (datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:30', '%H:%M')) + (datetime.strptime('11:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')) + (datetime.strptime('12:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')) + (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:30', '%H:%M')) + (datetime.strptime('16:00', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
        'Douglas': (datetime.strptime('09:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')) + (datetime.strptime('12:00', '%H:%M'), datetime.strptime('16:30', '%H:%M')),
        'Ryan': (datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')) + (datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:00', '%H:%M')) + (datetime.strptime('14:30', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
    }

    duration = 30
    meeting_time = schedule_meeting(start_time, end_time, schedules, duration)
    if meeting_time:
        print(f'Time: {meeting_time[0].strftime("%H:%M")} - {meeting_time[1].strftime("%H:%M")}, Day: {day_of_week}')
    else:
        print('No available time found.')

if __name__ == '__main__':
    main()