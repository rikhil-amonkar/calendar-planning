import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def calculate_schedule():
    # Define travel times as a dictionary of dictionaries
    travel_times = {
        'The Castro': {
            'Presidio': 20,
            'Sunset District': 17,
            'Haight-Ashbury': 6,
            'Mission District': 7,
            'Golden Gate Park': 11,
            'Russian Hill': 18
        },
        'Presidio': {
            'The Castro': 21,
            'Sunset District': 15,
            'Haight-Ashbury': 15,
            'Mission District': 26,
            'Golden Gate Park': 12,
            'Russian Hill': 14
        },
        'Sunset District': {
            'The Castro': 17,
            'Presidio': 16,
            'Haight-Ashbury': 15,
            'Mission District': 24,
            'Golden Gate Park': 11,
            'Russian Hill': 24
        },
        'Haight-Ashbury': {
            'The Castro': 6,
            'Presidio': 15,
            'Sunset District': 15,
            'Mission District': 11,
            'Golden Gate Park': 7,
            'Russian Hill': 17
        },
        'Mission District': {
            'The Castro': 7,
            'Presidio': 25,
            'Sunset District': 24,
            'Haight-Ashbury': 12,
            'Golden Gate Park': 17,
            'Russian Hill': 15
        },
        'Golden Gate Park': {
            'The Castro': 13,
            'Presidio': 11,
            'Sunset District': 10,
            'Haight-Ashbury': 7,
            'Mission District': 17,
            'Russian Hill': 19
        },
        'Russian Hill': {
            'The Castro': 21,
            'Presidio': 14,
            'Sunset District': 23,
            'Haight-Ashbury': 17,
            'Mission District': 16,
            'Golden Gate Park': 21
        }
    }

    # Define friends' availability and constraints
    friends = [
        {
            'name': 'Rebecca',
            'location': 'Presidio',
            'start': time_to_minutes('18:15'),
            'end': time_to_minutes('20:45'),
            'duration': 60
        },
        {
            'name': 'Linda',
            'location': 'Sunset District',
            'start': time_to_minutes('15:30'),
            'end': time_to_minutes('19:45'),
            'duration': 30
        },
        {
            'name': 'Elizabeth',
            'location': 'Haight-Ashbury',
            'start': time_to_minutes('17:15'),
            'end': time_to_minutes('19:30'),
            'duration': 105
        },
        {
            'name': 'William',
            'location': 'Mission District',
            'start': time_to_minutes('13:15'),
            'end': time_to_minutes('19:30'),
            'duration': 30
        },
        {
            'name': 'Robert',
            'location': 'Golden Gate Park',
            'start': time_to_minutes('14:15'),
            'end': time_to_minutes('21:30'),
            'duration': 45
        },
        {
            'name': 'Mark',
            'location': 'Russian Hill',
            'start': time_to_minutes('10:00'),
            'end': time_to_minutes('21:15'),
            'duration': 75
        }
    ]

    current_location = 'The Castro'
    current_time = time_to_minutes('9:00')
    itinerary = []
    remaining_friends = friends.copy()

    # Helper function to find the next best friend to meet
    def find_next_friend(current_loc, current_t, remaining):
        best_friend = None
        best_start = None
        best_end = None
        best_travel = None

        for friend in remaining:
            travel_time = travel_times[current_loc][friend['location']
            earliest_arrival = current_t + travel_time
            latest_departure = friend['end'] - friend['duration']

            if earliest_arrival > latest_departure:
                continue  # Can't meet this friend

            start_time = max(earliest_arrival, friend['start'])
            end_time = start_time + friend['duration']

            if end_time > friend['end']:
                continue  # Can't meet for full duration

            # Prefer friends with earliest possible start time
            if best_friend is None or start_time < best_start:
                best_friend = friend
                best_start = start_time
                best_end = end_time
                best_travel = travel_time

        return best_friend, best_start, best_end, best_travel

    # Schedule meetings greedily
    while remaining_friends:
        next_friend, start, end, travel = find_next_friend(current_location, current_time, remaining_friends)
        if not next_friend:
            break

        itinerary.append({
            'action': 'travel',
            'location': next_friend['location'],
            'person': None,
            'start_time': minutes_to_time(current_time),
            'end_time': minutes_to_time(current_time + travel)
        })

        itinerary.append({
            'action': 'meet',
            'location': next_friend['location'],
            'person': next_friend['name'],
            'start_time': minutes_to_time(start),
            'end_time': minutes_to_time(end)
        })

        current_location = next_friend['location']
        current_time = end
        remaining_friends.remove(next_friend)

    output = {
        'itinerary': itinerary
    }

    return json.dumps(output, indent=2)

print(calculate_schedule())