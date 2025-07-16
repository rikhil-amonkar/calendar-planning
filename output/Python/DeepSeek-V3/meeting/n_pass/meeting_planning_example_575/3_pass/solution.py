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

    def find_schedule(current_location, current_time, remaining_friends, itinerary):
        if not remaining_friends:
            return itinerary
        
        for i, friend in enumerate(remaining_friends):
            travel_time = travel_times[current_location][friend['location']]
            earliest_arrival = current_time + travel_time
            latest_departure = friend['end'] - friend['duration']
            
            if earliest_arrival > latest_departure:
                continue
                
            start_time = max(earliest_arrival, friend['start'])
            end_time = start_time + friend['duration']
            
            if end_time > friend['end']:
                continue
                
            new_itinerary = itinerary.copy()
            new_itinerary.append({
                'action': 'travel',
                'location': friend['location'],
                'person': None,
                'start_time': minutes_to_time(current_time),
                'end_time': minutes_to_time(current_time + travel_time)
            })
            
            new_itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(start_time),
                'end_time': minutes_to_time(end_time)
            })
            
            new_remaining = remaining_friends.copy()
            new_remaining.pop(i)
            
            result = find_schedule(friend['location'], end_time, new_remaining, new_itinerary)
            if result is not None:
                return result
                
        return None

    # Start with all friends remaining at The Castro at 9:00
    initial_location = 'The Castro'
    initial_time = time_to_minutes('9:00')
    result = find_schedule(initial_location, initial_time, friends, [])
    
    if result is None:
        return json.dumps({"error": "No valid schedule found that meets all constraints"}, indent=2)
    
    output = {
        'itinerary': result
    }

    return json.dumps(output, indent=2)

print(calculate_schedule())