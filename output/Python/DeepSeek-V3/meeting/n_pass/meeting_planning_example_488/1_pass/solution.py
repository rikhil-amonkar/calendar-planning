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
    # Travel times in minutes (from -> to)
    travel_times = {
        'Pacific Heights': {
            'Nob Hill': 8,
            'Russian Hill': 7,
            'The Castro': 16,
            'Sunset District': 21,
            'Haight-Ashbury': 11
        },
        'Nob Hill': {
            'Pacific Heights': 8,
            'Russian Hill': 5,
            'The Castro': 17,
            'Sunset District': 25,
            'Haight-Ashbury': 13
        },
        'Russian Hill': {
            'Pacific Heights': 7,
            'Nob Hill': 5,
            'The Castro': 21,
            'Sunset District': 23,
            'Haight-Ashbury': 17
        },
        'The Castro': {
            'Pacific Heights': 16,
            'Nob Hill': 16,
            'Russian Hill': 18,
            'Sunset District': 17,
            'Haight-Ashbury': 6
        },
        'Sunset District': {
            'Pacific Heights': 21,
            'Nob Hill': 27,
            'Russian Hill': 24,
            'The Castro': 17,
            'Haight-Ashbury': 15
        },
        'Haight-Ashbury': {
            'Pacific Heights': 12,
            'Nob Hill': 15,
            'Russian Hill': 17,
            'The Castro': 6,
            'Sunset District': 15
        }
    }

    # Friend constraints
    friends = {
        'Ronald': {
            'location': 'Nob Hill',
            'available_start': time_to_minutes('10:00'),
            'available_end': time_to_minutes('17:00'),
            'duration': 105
        },
        'Sarah': {
            'location': 'Russian Hill',
            'available_start': time_to_minutes('7:15'),
            'available_end': time_to_minutes('9:30'),
            'duration': 45
        },
        'Helen': {
            'location': 'The Castro',
            'available_start': time_to_minutes('13:30'),
            'available_end': time_to_minutes('17:00'),
            'duration': 120
        },
        'Joshua': {
            'location': 'Sunset District',
            'available_start': time_to_minutes('14:15'),
            'available_end': time_to_minutes('19:30'),
            'duration': 90
        },
        'Margaret': {
            'location': 'Haight-Ashbury',
            'available_start': time_to_minutes('10:15'),
            'available_end': time_to_minutes('22:00'),
            'duration': 60
        }
    }

    current_time = time_to_minutes('9:00')
    current_location = 'Pacific Heights'
    itinerary = []
    remaining_friends = list(friends.keys())

    # Try to meet Sarah first since she's only available early
    if 'Sarah' in remaining_friends:
        sarah = friends['Sarah']
        travel_time = travel_times[current_location][sarah['location']]
        arrival_time = current_time + travel_time
        if arrival_time <= sarah['available_end'] - sarah['duration']:
            start_time = max(arrival_time, sarah['available_start'])
            end_time = start_time + sarah['duration']
            itinerary.append({
                'action': 'meet',
                'location': sarah['location'],
                'person': 'Sarah',
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            })
            current_time = end_time
            current_location = sarah['location']
            remaining_friends.remove('Sarah')

    # Now try to meet Ronald, Helen, Joshua, Margaret in different orders
    best_itinerary = []
    max_meetings = 0

    for order in permutations(remaining_friends):
        temp_itinerary = itinerary.copy()
        temp_time = current_time
        temp_location = current_location
        temp_meetings = len(temp_itinerary)

        for friend_name in order:
            friend = friends[friend_name]
            travel_time = travel_times[temp_location][friend['location']]
            arrival_time = temp_time + travel_time
            latest_start = friend['available_end'] - friend['duration']
            if arrival_time > latest_start:
                continue  # Can't meet this friend in this order
            start_time = max(arrival_time, friend['available_start'])
            end_time = start_time + friend['duration']
            temp_itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend_name,
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            })
            temp_time = end_time
            temp_location = friend['location']
            temp_meetings += 1

        if temp_meetings > max_meetings:
            max_meetings = temp_meetings
            best_itinerary = temp_itinerary

    if not best_itinerary:
        best_itinerary = itinerary  # Only Sarah if no other meetings possible

    return {'itinerary': best_itinerary}

if __name__ == '__main__':
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))