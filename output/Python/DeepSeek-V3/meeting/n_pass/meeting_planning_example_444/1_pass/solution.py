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
    # Travel times in minutes (from: {to: time})
    travel_times = {
        'Financial District': {
            'Russian Hill': 10,
            'Sunset District': 31,
            'North Beach': 7,
            'The Castro': 23,
            'Golden Gate Park': 23
        },
        'Russian Hill': {
            'Financial District': 11,
            'Sunset District': 23,
            'North Beach': 5,
            'The Castro': 21,
            'Golden Gate Park': 21
        },
        'Sunset District': {
            'Financial District': 30,
            'Russian Hill': 24,
            'North Beach': 29,
            'The Castro': 17,
            'Golden Gate Park': 11
        },
        'North Beach': {
            'Financial District': 8,
            'Russian Hill': 4,
            'Sunset District': 27,
            'The Castro': 22,
            'Golden Gate Park': 22
        },
        'The Castro': {
            'Financial District': 20,
            'Russian Hill': 18,
            'Sunset District': 17,
            'North Beach': 20,
            'Golden Gate Park': 13
        },
        'Golden Gate Park': {
            'Financial District': 26,
            'Russian Hill': 19,
            'Sunset District': 10,
            'North Beach': 24,
            'The Castro': 13
        }
    }

    # Friend constraints
    friends = [
        {
            'name': 'Ronald',
            'location': 'Russian Hill',
            'available_start': time_to_minutes('13:45'),
            'available_end': time_to_minutes('17:15'),
            'duration': 105
        },
        {
            'name': 'Patricia',
            'location': 'Sunset District',
            'available_start': time_to_minutes('9:15'),
            'available_end': time_to_minutes('22:00'),
            'duration': 60
        },
        {
            'name': 'Laura',
            'location': 'North Beach',
            'available_start': time_to_minutes('12:30'),
            'available_end': time_to_minutes('12:45'),
            'duration': 15
        },
        {
            'name': 'Emily',
            'location': 'The Castro',
            'available_start': time_to_minutes('16:15'),
            'available_end': time_to_minutes('18:30'),
            'duration': 60
        },
        {
            'name': 'Mary',
            'location': 'Golden Gate Park',
            'available_start': time_to_minutes('15:00'),
            'available_end': time_to_minutes('16:30'),
            'duration': 60
        }
    ]

    current_time = time_to_minutes('9:00')
    current_location = 'Financial District'
    best_itinerary = []
    max_meetings = 0

    # Generate all possible orders to meet friends
    for friend_order in permutations(friends):
        itinerary = []
        temp_time = current_time
        temp_location = current_location
        meetings = 0

        for friend in friend_order:
            # Calculate travel time to friend's location
            travel_time = travel_times[temp_location][friend['location']]
            arrival_time = temp_time + travel_time

            # Check if we can meet within the friend's availability
            meeting_start = max(arrival_time, friend['available_start'])
            meeting_end = meeting_start + friend['duration']

            if meeting_end <= friend['available_end']:
                itinerary.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                meetings += 1
                temp_time = meeting_end
                temp_location = friend['location']
            else:
                break  # Can't meet this friend in this order

        if meetings > max_meetings:
            max_meetings = meetings
            best_itinerary = itinerary

    return {'itinerary': best_itinerary}

if __name__ == '__main__':
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))