from datetime import datetime, timedelta

def find_meeting_time(participants, duration):
    # Sort participants by their earliest available time
    participants.sort(key=lambda x: x['start'])

    # Initialize the proposed meeting time
    proposed_time = participants[0]['start']

    # Check if the proposed time works for all participants
    while proposed_time < datetime(2024, 1, 1, 17, 0):  # assuming the day is Monday
        works = True
        for participant in participants:
            if (proposed_time >= participant['start'] and proposed_time + timedelta(minutes=duration) <= participant['end']):
                works = False
                break
        if works:
            # Check for unavailable time slots
            unavailable_slots = [slot for participant in participants for slot in [participant['start'] + timedelta(minutes=i*30), participant['start'] + timedelta(minutes=(i+1)*30-1)] for i in range(int((participant['end'] - participant['start']).total_seconds()/30))]
            if all(proposed_time not in unavailable_slots and (proposed_time + timedelta(minutes=duration)) not in unavailable_slots):
                return proposed_time.strftime("%H:%M") + "-" + (proposed_time + timedelta(minutes=duration)).strftime("%H:%M") + " " + proposed_time.strftime("%A")
        proposed_time += timedelta(minutes=1)

# Define the participants' schedules
participants = [
    {'name': 'Gregory','start': datetime(2024, 1, 1, 9, 0), 'end': datetime(2024, 1, 1, 10, 0)},
    {'name': 'Gregory','start': datetime(2024, 1, 1, 10, 30), 'end': datetime(2024, 1, 1, 11, 30)},
    {'name': 'Gregory','start': datetime(2024, 1, 1, 12, 30), 'end': datetime(2024, 1, 1, 13, 0)},
    {'name': 'Gregory','start': datetime(2024, 1, 1, 13, 30), 'end': datetime(2024, 1, 1, 14, 0)},
    {'name': 'Natalie','start': datetime(2024, 1, 1, 0, 0), 'end': datetime(2024, 1, 1, 17, 0)},
    {'name': 'Christine','start': datetime(2024, 1, 1, 9, 0), 'end': datetime(2024, 1, 1, 11, 30)},
    {'name': 'Christine','start': datetime(2024, 1, 1, 13, 30), 'end': datetime(2024, 1, 1, 17, 0)},
    {'name': 'Vincent','start': datetime(2024, 1, 1, 9, 0), 'end': datetime(2024, 1, 1, 9, 30)},
    {'name': 'Vincent','start': datetime(2024, 1, 1, 10, 30), 'end': datetime(2024, 1, 1, 12, 0)},
    {'name': 'Vincent','start': datetime(2024, 1, 1, 12, 30), 'end': datetime(2024, 1, 1, 14, 0)},
    {'name': 'Vincent','start': datetime(2024, 1, 1, 14, 30), 'end': datetime(2024, 1, 1, 17, 0)},
    {'name': 'Unavailable Participant','start': datetime(2024, 1, 1, 17, 0), 'end': datetime(2024, 1, 1, 24, 0)},
]

# Find the meeting time
duration = 30  # minutes
print(find_meeting_time(participants, duration))