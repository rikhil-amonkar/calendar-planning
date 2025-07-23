import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def calculate_schedule():
    # Define travel times as a dictionary of dictionaries
    travel_times = {
        'Embarcadero': {
            'Richmond District': 21,
            'Union Square': 10,
            'Financial District': 5,
            'Pacific Heights': 11,
            'Nob Hill': 10,
            'Bayview': 21
        },
        'Richmond District': {
            'Embarcadero': 19,
            'Union Square': 21,
            'Financial District': 22,
            'Pacific Heights': 10,
            'Nob Hill': 17,
            'Bayview': 26
        },
        'Union Square': {
            'Embarcadero': 11,
            'Richmond District': 20,
            'Financial District': 9,
            'Pacific Heights': 15,
            'Nob Hill': 9,
            'Bayview': 15
        },
        'Financial District': {
            'Embarcadero': 4,
            'Richmond District': 21,
            'Union Square': 9,
            'Pacific Heights': 13,
            'Nob Hill': 8,
            'Bayview': 19
        },
        'Pacific Heights': {
            'Embarcadero': 10,
            'Richmond District': 12,
            'Union Square': 12,
            'Financial District': 13,
            'Nob Hill': 8,
            'Bayview': 22
        },
        'Nob Hill': {
            'Embarcadero': 9,
            'Richmond District': 14,
            'Union Square': 7,
            'Financial District': 9,
            'Pacific Heights': 8,
            'Bayview': 19
        },
        'Bayview': {
            'Embarcadero': 19,
            'Richmond District': 25,
            'Union Square': 17,
            'Financial District': 19,
            'Pacific Heights': 23,
            'Nob Hill': 20
        }
    }

    # Define friends' availability and constraints
    friends = [
        {
            'name': 'Kenneth',
            'location': 'Richmond District',
            'start': time_to_minutes('21:15'),  # 9:15PM
            'end': time_to_minutes('22:00'),     # 10:00PM
            'duration': 30
        },
        {
            'name': 'Lisa',
            'location': 'Union Square',
            'start': time_to_minutes('9:00'),
            'end': time_to_minutes('16:30'),
            'duration': 45
        },
        {
            'name': 'Joshua',
            'location': 'Financial District',
            'start': time_to_minutes('12:00'),
            'end': time_to_minutes('15:15'),
            'duration': 15
        },
        {
            'name': 'Nancy',
            'location': 'Pacific Heights',
            'start': time_to_minutes('8:00'),
            'end': time_to_minutes('11:30'),
            'duration': 90
        },
        {
            'name': 'Andrew',
            'location': 'Nob Hill',
            'start': time_to_minutes('11:30'),
            'end': time_to_minutes('20:15'),
            'duration': 60
        },
        {
            'name': 'John',
            'location': 'Bayview',
            'start': time_to_minutes('16:45'),
            'end': time_to_minutes('21:30'),
            'duration': 75
        }
    ]

    # Filter friends that can be visited (excluding those with impossible time windows)
    possible_friends = [f for f in friends if f['end'] - f['start'] >= f['duration']]

    # Generate all possible orders of visiting friends (permutations)
    best_schedule = None
    max_meetings = 0

    for friend_order in permutations(possible_friends):
        current_location = 'Embarcadero'
        current_time = time_to_minutes('9:00')
        schedule = []
        meetings = 0

        for friend in friend_order:
            # Calculate travel time to friend's location
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time

            # Check if we can meet the friend
            meeting_start = max(arrival_time, friend['start'])
            meeting_end = meeting_start + friend['duration']

            if meeting_end <= friend['end']:
                schedule.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                meetings += 1
                current_time = meeting_end
                current_location = friend['location']
            else:
                break  # Can't meet this friend in this order

        # Check if this schedule is better than the current best
        if meetings > max_meetings or (meetings == max_meetings and best_schedule is None):
            max_meetings = meetings
            best_schedule = schedule

    # After evaluating all permutations, return the best schedule
    if best_schedule is None:
        return {'itinerary': []}
    else:
        return {'itinerary': best_schedule}

# Calculate and print the optimal schedule
result = calculate_schedule()
print(json.dumps(result, indent=2))