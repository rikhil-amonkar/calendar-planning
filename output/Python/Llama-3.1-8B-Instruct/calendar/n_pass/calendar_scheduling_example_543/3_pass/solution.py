from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, meeting_duration, schedules):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
    start_time (str): Start time of the work hours (e.g., '09:00').
    end_time (str): End time of the work hours (e.g., '17:00').
    meeting_duration (int): Duration of the meeting in minutes.
    schedules (dict): Existing schedules for each participant.

    Returns:
    str: A proposed time range in the format HH:MM-HH:MM and the day of the week.
    """
    # Convert time strings to datetime objects
    start_time = datetime.strptime(start_time, '%H:%M')
    end_time = datetime.strptime(end_time, '%H:%M')

    # Generate a list of time slots in minutes
    time_slots = [(start_time + timedelta(minutes=i)).strftime('%H:%M') for i in range((end_time - start_time).seconds // 60 + 1)]

    # Filter out time slots that are not available for any participant
    available_time_slots = []
    for time_slot in time_slots:
        is_available = True
        for participant, schedule in schedules.items():
            for start, end in schedule:
                start = datetime.strptime(start, '%H:%M')
                end = datetime.strptime(end, '%H:%M')
                if start <= datetime.strptime(time_slot, '%H:%M') < end:
                    is_available = False
                    break
            if not is_available:
                break
        if is_available:
            available_time_slots.append(time_slot)

    # Find a suitable time slot that is long enough for the meeting
    suitable_time_slots = []
    for i in range(len(available_time_slots)):
        for j in range(i + 1, len(available_time_slots) + 1):
            time_slot_range = '-'.join(available_time_slots[i:j])
            start_time_slot = datetime.strptime(available_time_slots[i], '%H:%M')
            end_time_slot = datetime.strptime(available_time_slots[j-1], '%H:%M')
            if (end_time_slot - start_time_slot).seconds // 60 >= meeting_duration:
                suitable_time_slots.append(time_slot_range)

    # If no suitable time slot is found, return an error message
    if not suitable_time_slots:
        return 'No suitable time slot found.'

    # Find the earliest suitable time slot that starts on the hour
    proposed_time = min([slot for slot in suitable_time_slots if slot.split('-')[0].endswith(':00')])

    # Format the proposed time as a time range
    start_time_slot = proposed_time.split('-')[0]
    end_time_slot = (datetime.strptime(start_time_slot, "%H:%M") + timedelta(minutes=meeting_duration)).strftime("%H:%M")
    proposed_time_range = f'{start_time_slot}-{end_time_slot}'

    # Return the proposed time range and the day of the week
    return f'{proposed_time_range} on {start_time.strftime("%A")}'

# Example usage
schedules = {
    'James': [('11:30', '12:00'), ('14:30', '15:00')],
    'John': [('9:30', '11:00'), ('11:30', '12:00'), ('12:30', '13:30'), ('14:30', '16:30')]
}

print(find_meeting_time('09:00', '17:00', 60, schedules))