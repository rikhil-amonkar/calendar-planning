from datetime import datetime, timedelta

def find_meeting_time(day, start_time, end_time, durations, schedules, preferences):
    # Convert day to a datetime object
    day = datetime.strptime(day, '%A').weekday()
    start_time = datetime.strptime(start_time, '%H:%M')
    end_time = datetime.strptime(end_time, '%H:%M')

    # Create a list to store available time slots
    available_slots = []

    # Iterate over each hour in the day
    current_time = start_time
    while current_time < end_time:
        # Check if the current time slot is available for all participants
        is_available = True
        for participant, schedule in schedules.items():
            if current_time.hour * 60 + current_time.minute >= schedule[0].hour * 60 + schedule[0].minute and current_time.hour * 60 + current_time.minute <= schedule[0].hour * 60 + schedule[0].minute + (schedule[0].hour - schedule[0].minute):
                is_available = False
                break

        if is_available:
            # Check if the time slot is within the preferences of any participant
            for participant, preference in preferences.items():
                if current_time >= datetime.strptime(preference, '%H:%M') and current_time <= end_time:
                    is_available = False
                    break

        if is_available:
            # Add the available time slot to the list
            available_slots.append((current_time.strftime('%H:%M'), (current_time + timedelta(minutes=durations)).strftime('%H:%M')))

        # Move to the next hour
        current_time += timedelta(hours=1)

    # Find the first available time slot that is long enough for the meeting
    for slot in available_slots:
        if (datetime.strptime(slot[1], '%H:%M') - datetime.strptime(slot[0], '%H:%M')).total_seconds() / 60 >= durations:
            return slot[0] +'-'+ slot[1], day

    # If no available time slot is found, return None
    return None, day

def main():
    # Define the meeting duration
    duration = 30

    # Define the schedules and preferences
    schedules = {
        'Emily': [(10, 30), (11, 30), (14, 0), (16, 0), (16, 30)],
        'Melissa': [(9, 30), (14, 30)],
        'Frank': [(10, 0), (11, 0), (12, 30), (13, 30), (15, 0), (16, 30)]
    }
    preferences = {
        'Frank': '9:30'
    }

    # Find a suitable time for the meeting
    time, day = find_meeting_time('Monday', '9:00', '17:00', duration, schedules, preferences)

    # Print the result
    if time:
        print(f'{day}, {time}')
    else:
        print('No available time slot found.')

if __name__ == '__main__':
    main()