import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def calculate_schedule():
    # Travel times in minutes (from -> to)
    travel_times = {
        'Pacific Heights': {
            'North Beach': 9,
            'Financial District': 13,
            'Alamo Square': 10,
            'Mission District': 15
        },
        'North Beach': {
            'Pacific Heights': 8,
            'Financial District': 8,
            'Alamo Square': 16,
            'Mission District': 18
        },
        'Financial District': {
            'Pacific Heights': 13,
            'North Beach': 7,
            'Alamo Square': 17,
            'Mission District': 17
        },
        'Alamo Square': {
            'Pacific Heights': 10,
            'North Beach': 15,
            'Financial District': 17,
            'Mission District': 10
        },
        'Mission District': {
            'Pacific Heights': 16,
            'North Beach': 17,
            'Financial District': 17,
            'Alamo Square': 11
        }
    }

    # Constraints
    start_location = 'Pacific Heights'
    start_time = time_to_minutes('9:00')

    friends = [
        {
            'name': 'Helen',
            'location': 'North Beach',
            'available_start': time_to_minutes('9:00'),
            'available_end': time_to_minutes('17:00'),
            'min_duration': 15
        },
        {
            'name': 'Kevin',
            'location': 'Mission District',
            'available_start': time_to_minutes('10:45'),
            'available_end': time_to_minutes('14:45'),
            'min_duration': 45
        },
        {
            'name': 'Amanda',
            'location': 'Alamo Square',
            'available_start': time_to_minutes('19:45'),
            'available_end': time_to_minutes('21:00'),
            'min_duration': 60
        },
        {
            'name': 'Betty',
            'location': 'Financial District',
            'available_start': time_to_minutes('19:00'),
            'available_end': time_to_minutes('21:45'),
            'min_duration': 90
        }
    ]

    # Generate all possible meeting orders (permutations)
    best_itinerary = []
    max_meetings = 0

    for order in permutations(friends):
        current_location = start_location
        current_time = start_time
        itinerary = []
        meetings = 0

        for friend in order:
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time

            # Calculate meeting window
            meeting_start = max(arrival_time, friend['available_start'])
            meeting_end = min(meeting_start + friend['min_duration'], friend['available_end'])

            if meeting_end - meeting_start >= friend['min_duration']:
                meetings += 1
                itinerary.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                current_time = meeting_end
                current_location = friend['location']

        if meetings > max_meetings or (meetings == max_meetings and len(itinerary) > len(best_itinerary)):
            max_meetings = meetings
            best_itinerary = itinerary
            if max_meetings == len(friends):
                break  # Found optimal solution

    # If we didn't find a way to meet all friends, try to add remaining ones
    if max_meetings < len(friends):
        remaining_friends = [f for f in friends if f['name'] not in [m['person'] for m in best_itinerary]]
        current_location = best_itinerary[-1]['location'] if best_itinerary else start_location
        current_time = time_to_minutes(best_itinerary[-1]['end_time']) if best_itinerary else start_time

        for friend in remaining_friends:
            travel_time = travel_times[current_location][friend['location']]
            arrival_time = current_time + travel_time

            meeting_start = max(arrival_time, friend['available_start'])
            meeting_end = min(meeting_start + friend['min_duration'], friend['available_end'])

            if meeting_end - meeting_start >= friend['min_duration']:
                best_itinerary.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(meeting_start),
                    'end_time': minutes_to_time(meeting_end)
                })
                current_time = meeting_end
                current_location = friend['location']

    return {"itinerary": best_itinerary}

result = calculate_schedule()
print(json.dumps(result, indent=2))