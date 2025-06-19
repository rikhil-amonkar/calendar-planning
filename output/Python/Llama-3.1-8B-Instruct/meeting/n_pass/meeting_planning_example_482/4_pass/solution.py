import json
from datetime import datetime, timedelta

# Define travel distances in minutes
travel_distances = {
    'Haight-Ashbury': {
        'Mission District': 11,
        'Bayview': 18,
        'Pacific Heights': 12,
        'Russian Hill': 17,
        'Fisherman\'s Wharf': 23
    },
    'Mission District': {
        'Haight-Ashbury': 12,
        'Bayview': 15,
        'Pacific Heights': 16,
        'Russian Hill': 15,
        'Fisherman\'s Wharf': 22
    },
    'Bayview': {
        'Haight-Ashbury': 19,
        'Mission District': 13,
        'Pacific Heights': 23,
        'Russian Hill': 23,
        'Fisherman\'s Wharf': 25
    },
    'Pacific Heights': {
        'Haight-Ashbury': 11,
        'Mission District': 15,
        'Bayview': 22,
        'Russian Hill': 7,
        'Fisherman\'s Wharf': 13
    },
    'Russian Hill': {
        'Haight-Ashbury': 17,
        'Mission District': 16,
        'Bayview': 23,
        'Pacific Heights': 7,
        'Fisherman\'s Wharf': 7
    },
    'Fisherman\'s Wharf': {
        'Haight-Ashbury': 22,
        'Mission District': 22,
        'Bayview': 26,
        'Pacific Heights': 12,
        'Russian Hill': 7
    }
}

# Define meeting constraints
constraints = {
    'Stephanie': {'location': 'Mission District','start_time': '08:15', 'end_time': '13:45','meeting_time': 90},
    'Sandra': {'location': 'Bayview','start_time': '13:00', 'end_time': '19:30','meeting_time': 15},
    'Richard': {'location': 'Pacific Heights','start_time': '07:15', 'end_time': '10:15','meeting_time': 75},
    'Brian': {'location': 'Russian Hill','start_time': '12:15', 'end_time': '16:00','meeting_time': 120},
    'Jason': {'location': 'Fisherman\'s Wharf','start_time': '08:30', 'end_time': '17:45','meeting_time': 60}
}

def calculate_meeting_schedule():
    # Initialize schedule
    schedule = []

    # Sort the constraints by start time
    sorted_constraints = sorted(constraints.items(), key=lambda x: datetime.strptime(x[1]['start_time'], '%H:%M'))

    # Start at Haight-Ashbury at 9:00 AM
    current_location = 'Haight-Ashbury'
    current_time = datetime.strptime('09:00', '%H:%M')

    # Iterate over the sorted constraints
    for person, constraint in sorted_constraints:
        # Calculate the meeting time
        meeting_time = datetime.strptime(constraint['start_time'], '%H:%M') + timedelta(minutes=constraint['meeting_time'])

        # Check if the meeting time exceeds the available time
        if meeting_time > datetime.strptime(constraint['end_time'], '%H:%M'):
            # If Brian's meeting time exceeds his available time, adjust the schedule
            if person == 'Brian':
                # Move Brian's meeting to the next available time slot
                constraint['start_time'] = '16:00'
                constraint['end_time'] = '17:00'
                constraint['meeting_time'] = 60
            else:
                raise ValueError(f"Meeting time for {person} exceeds available time")

        # Calculate the travel time
        travel_time = timedelta(minutes=travel_distances[current_location][constraint['location']])

        # Add the meeting to the schedule
        schedule.append({
            'action':'meet',
            'location': constraint['location'],
            'person': person,
          'start_time': current_time.strftime('%H:%M'),
            'end_time': (current_time + timedelta(minutes=constraint['meeting_time'])).strftime('%H:%M')
        })

        # Update the current location and time
        current_location = constraint['location']
        current_time = datetime.strptime(constraint['start_time'], '%H:%M') + timedelta(minutes=constraint['meeting_time'])
        current_time += travel_time

    return schedule

def main():
    schedule = calculate_meeting_schedule()
    print(json.dumps({'itinerary': schedule}, indent=4))

if __name__ == '__main__':
    main()