from datetime import datetime, timedelta

def schedule_meeting(participants, start_time, end_time, duration, preferences=None):
    # Initialize the meeting time
    meeting_time = start_time + timedelta(hours=0, minutes=0)

    while meeting_time < end_time:
        # Check if all participants are available at the meeting time
        if all(
            not (meeting_time + timedelta(minutes=duration)).time() < participant['busy'][i]['end'].time()
            and not (meeting_time - timedelta(minutes=duration)).time() > participant['busy'][i]['start'].time()
            for i in range(len(participant['busy']))
        ):
            # Check if the meeting time meets any participant's preference
            if all(
                not (meeting_time + timedelta(minutes=duration)).time() < participant['preference']['end'].time()
                and not (meeting_time - timedelta(minutes=duration)).time() > participant['preference']['start'].time()
                for participant in participants
            ):
                # Return the meeting time if it meets all conditions
                return f"{meeting_time.strftime('%H:%M')} - {(meeting_time + timedelta(minutes=duration)).strftime('%H:%M')} on {start_time.strftime('%A')}"

        # Move to the next available time slot
        meeting_time += timedelta(minutes=30)

    # Return None if no meeting time is found
    return None

# Define the participants' schedules
participants = {
    'Natalie': {'busy': []},
    'David': {'busy': [{'start': datetime(2024, 7, 22, 11, 30), 'end': datetime(2024, 7, 22, 12, 0)}, {'start': datetime(2024, 7, 22, 14, 30), 'end': datetime(2024, 7, 22, 15, 0)}], 'preference': {'start': datetime(2024, 7, 22, 14, 0), 'end': datetime(2024, 7, 22, 17, 0)}},
    'Douglas': {'busy': [{'start': datetime(2024, 7, 22, 9, 30), 'end': datetime(2024, 7, 22, 10, 0)}, {'start': datetime(2024, 7, 22, 11, 30), 'end': datetime(2024, 7, 22, 12, 0)}, {'start': datetime(2024, 7, 22, 13, 0), 'end': datetime(2024, 7, 22, 13, 30)}, {'start': datetime(2024, 7, 22, 14, 30), 'end': datetime(2024, 7, 22, 15, 0)}]},
    'Ralph': {'busy': [{'start': datetime(2024, 7, 22, 9, 0), 'end': datetime(2024, 7, 22, 9, 30)}, {'start': datetime(2024, 7, 22, 10, 0), 'end': datetime(2024, 7, 22, 11, 0)}, {'start': datetime(2024, 7, 22, 11, 30), 'end': datetime(2024, 7, 22, 12, 30)}, {'start': datetime(2024, 7, 22, 13, 30), 'end': datetime(2024, 7, 22, 15, 0)}, {'start': datetime(2024, 7, 22, 15, 30), 'end': datetime(2024, 7, 22, 16, 0)}, {'start': datetime(2024, 7, 22, 16, 30), 'end': datetime(2024, 7, 22, 17, 0)}]},
    'Jordan': {'busy': [{'start': datetime(2024, 7, 22, 9, 0), 'end': datetime(2024, 7, 22, 10, 0)}, {'start': datetime(2024, 7, 22, 12, 0), 'end': datetime(2024, 7, 22, 12, 30)}, {'start': datetime(2024, 7, 22, 13, 0), 'end': datetime(2024, 7, 22, 13, 30)}, {'start': datetime(2024, 7, 22, 14, 30), 'end': datetime(2024, 7, 22, 15, 0)}, {'start': datetime(2024, 7, 22, 15, 30), 'end': datetime(2024, 7, 22, 17, 0)}]},
}

# Define the start and end time of the workday
start_time = datetime(2024, 7, 22, 9, 0)
end_time = datetime(2024, 7, 22, 17, 0)

# Define the meeting duration
duration = timedelta(hours=0, minutes=30)

# Find a suitable meeting time
meeting_time = schedule_meeting(participants.values(), start_time, end_time, duration)

# Print the result
if meeting_time:
    print(meeting_time)
else:
    print("No meeting time found.")