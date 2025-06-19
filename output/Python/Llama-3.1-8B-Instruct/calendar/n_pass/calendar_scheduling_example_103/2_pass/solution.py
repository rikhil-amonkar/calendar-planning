from datetime import datetime, timedelta

def find_available_time(start_time, end_time, blocks):
    """
    Find the first available time slot in the given time range, 
    avoiding the specified time blocks.
    
    Args:
    start_time (datetime): The start time of the time range.
    end_time (datetime): The end time of the time range.
    blocks (list): A list of time blocks to avoid.
    
    Returns:
    tuple: A tuple containing the start and end times of the available time slot.
    """
    current_time = start_time
    while current_time < end_time:
        # Check if the current time is not in any of the blocks
        if not any(block[0] <= current_time < block[1] for block in blocks):
            return current_time, current_time + timedelta(minutes=30)  # Meeting duration is 30 minutes
        current_time += timedelta(minutes=1)
    return None

def schedule_meeting(day, start_time, end_time, participants):
    """
    Schedule a meeting on the given day, avoiding the specified time blocks.
    
    Args:
    day (str): The day of the week.
    start_time (datetime): The start time of the work hours.
    end_time (datetime): The end time of the work hours.
    participants (dict): A dictionary of participants and their time blocks.
    
    Returns:
    tuple: A tuple containing the start and end times of the meeting, 
           and the day of the week.
    """
    available_time = find_available_time(start_time, end_time, [block for participant_blocks in participants.values() for block in participant_blocks])
    
    if available_time:
        return f"{day}, {available_time[0].strftime('%H:%M')}:{available_time[1].strftime('%H:%M')}"
    else:
        return "No available time found"

# Usage
start_time = datetime.strptime('09:00', '%H:%M')
end_time = datetime.strptime('17:00', '%H:%M')
day = "Monday"
participants = {
    'Diane': [(datetime.strptime('9:30', '%H:%M'), datetime.strptime('10:00', '%H:%M')),
              (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:00', '%H:%M'))],
    'Jack': [(datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
             (datetime.strptime('14:30', '%H:%M'), datetime.strptime('15:00', '%H:%M'))],
    'Eugene': [(datetime.strptime('9:00', '%H:%M'), datetime.strptime('10:00', '%H:%M')),
               (datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
               (datetime.strptime('12:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
               (datetime.strptime('15:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))],
    'Patricia': [(datetime.strptime('9:30', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
                 (datetime.strptime('11:00', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
                 (datetime.strptime('12:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
                 (datetime.strptime('15:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))]
}

print(schedule_meeting(day, start_time, end_time, participants))