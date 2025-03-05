from datetime import datetime, timedelta

def find_meeting_time(participants, start_time, end_time, meeting_duration, preferences=None):
    # Convert time to minutes
    start_time = datetime.strptime(start_time, '%H:%M')
    end_time = datetime.strptime(end_time, '%H:%M')
    start_time_in_minutes = start_time.hour * 60 + start_time.minute
    end_time_in_minutes = end_time.hour * 60 + end_time.minute

    # Initialize a list to store the busy times
    busy_times = []

    # Iterate over each participant's schedule
    for participant in participants:
        for schedule in participant['schedule']:
            # Convert schedule time to minutes
            schedule_start_time = datetime.strptime(schedule['start'], '%H:%M')
            schedule_end_time = datetime.strptime(schedule['end'], '%H:%M')
            schedule_start_time_in_minutes = schedule_start_time.hour * 60 + schedule_start_time.minute
            schedule_end_time_in_minutes = schedule_end_time.hour * 60 + schedule_end_time.minute

            # Add the busy time to the list
            busy_times.append((schedule_start_time_in_minutes, schedule_end_time_in_minutes))

    # Sort the busy times
    busy_times.sort()

    # Initialize the proposed meeting time
    proposed_meeting_time = None

    # Iterate over the time slots
    for time in range(start_time_in_minutes, end_time_in_minutes - meeting_duration + 1):
        # Assume the time slot is available
        is_available = True

        # Check if the time slot conflicts with any busy time
        for busy_time in busy_times:
            if time >= busy_time[0] and time + meeting_duration <= busy_time[1]:
                # If the time slot conflicts with a busy time, it's not available
                is_available = False
                break

        # Check if the time slot meets the preferences
        if preferences is not None:
            for preference in preferences:
                if preference['type'] == 'avoid_after' and time >= preference['time']:
                    is_available = False
                    break

        # If the time slot is available and meets the preferences, propose it as the meeting time
        if is_available:
            proposed_meeting_time = (time, time + meeting_duration)
            break

    # Convert the proposed meeting time back to hours and minutes
    proposed_meeting_start_time = datetime.strptime(str(proposed_meeting_time[0] // 60) + ':' + str(proposed_meeting_time[0] % 60), '%H:%M')
    proposed_meeting_end_time = datetime.strptime(str(proposed_meeting_time[1] // 60) + ':' + str(proposed_meeting_time[1] % 60), '%H:%M')

    # Return the proposed meeting time
    return '{' + proposed_meeting_start_time.strftime('%H:%M') + ':' + proposed_meeting_end_time.strftime('%H:%M') + '}'

# Define the participants and their schedules
participants = [
    {'name': 'Raymond','schedule': [{'start': '9:00', 'end': '9:30'}, {'start': '11:30', 'end': '12:00'}, {'start': '13:00', 'end': '13:30'}, {'start': '15:00', 'end': '15:30'}]},
    {'name': 'Billy','schedule': [{'start': '10:00', 'end': '10:30'}, {'start': '12:00', 'end': '13:00'}, {'start': '16:30', 'end': '17:00'}]},
    {'name': 'Donald','schedule': [{'start': '9:00', 'end': '9:30'}, {'start': '10:00', 'end': '11:00'}, {'start': '12:00', 'end': '13:00'}, {'start': '14:00', 'end': '14:30'}, {'start': '16:00', 'end': '17:00'}]}
]

# Define the meeting duration
meeting_duration = 30

# Define the start and end time of the work hours
start_time = '9:00'
end_time = '17:00'

# Define the preferences
preferences = [
    {'type': 'avoid_after', 'time': 15 * 60}  # Avoid meetings after 15:00
]

# Find the proposed meeting time
proposed_meeting_time = find_meeting_time(participants, start_time, end_time, meeting_duration, preferences)

# Print the proposed meeting time
print(proposed_meeting_time)