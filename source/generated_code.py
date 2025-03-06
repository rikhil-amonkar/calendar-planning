from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time, preferences=None):
    # Convert time to datetime objects
    start_time = datetime.strptime(start_time, '%H:%M')
    end_time = datetime.strptime(end_time, '%H:%M')

    # Calculate the end time of the meeting
    meeting_end_time = lambda start: start + timedelta(minutes=meeting_duration)

    # Initialize the proposed time
    proposed_time = None

    # Iterate over all possible times
    for hour in range(start_time.hour, end_time.hour + 1):
        for minute in range(0, 60):
            # Skip if the time is outside of work hours
            if (hour < start_time.hour or hour > end_time.hour) or \
               (hour == start_time.hour and minute < start_time.minute) or \
               (hour == end_time.hour and minute > end_time.minute):
                continue

            # Convert the current time to a datetime object
            current_time = datetime.strptime(f'{hour}:{minute}', '%H:%M')

            # Check if the current time works for all participants
            if all(is_available(participant, current_time, meeting_end_time(current_time)) for participant in participants):
                if preferences and 'avoid_after' in preferences and current_time >= datetime.strptime(preferences['avoid_after'], '%H:%M'):
                    continue
                proposed_time = f'{{{current_time.strftime("%H:%M"):}:{meeting_end_time(current_time).strftime("%H:%M")}}}'
                break

        # If a proposed time is found, break the loop
        if proposed_time:
            break

    return proposed_time


def is_available(participant, start_time, end_time):
    for busy_time in participant['busy']:
        busy_start_time = datetime.strptime(busy_time['start'], '%H:%M')
        busy_end_time = datetime.strptime(busy_time['end'], '%H:%M')

        # Check if the proposed time overlaps with the busy time
        if (start_time >= busy_start_time and start_time < busy_end_time) or \
           (end_time > busy_start_time and end_time <= busy_end_time) or \
           (start_time <= busy_start_time and end_time >= busy_end_time):
            return False

    return True


# Example usage
participants = [
    {'name': 'Raymond', 'busy': [{'start': '09:00', 'end': '09:30'}, {'start': '11:30', 'end': '12:00'}, {'start': '13:00', 'end': '13:30'}, {'start': '15:00', 'end': '15:30'}]},
    {'name': 'Billy', 'busy': [{'start': '10:00', 'end': '10:30'}, {'start': '12:00', 'end': '13:00'}, {'start': '16:30', 'end': '17:00'}]},
    {'name': 'Donald', 'busy': [{'start': '09:00', 'end': '09:30'}, {'start': '10:00', 'end': '11:00'}, {'start': '12:00', 'end': '13:00'}, {'start': '14:00', 'end': '14:30'}, {'start': '16:00', 'end': '17:00'}]}
]

meeting_duration = 30
start_time = '09:00'
end_time = '17:00'
preferences = {'avoid_after': '15:00'}

proposed_time = find_meeting_time(participants, meeting_duration, start_time, end_time, preferences)
print(proposed_time)