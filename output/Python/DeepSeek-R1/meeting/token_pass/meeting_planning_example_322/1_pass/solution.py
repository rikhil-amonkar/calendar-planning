import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    return hour * 60 + minute

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    travel_times = {
        'Sunset District': {
            'Russian Hill': 24,
            'Chinatown': 30,
            'Presidio': 16,
            'Fisherman\'s Wharf': 29
        },
        'Russian Hill': {
            'Sunset District': 23,
            'Chinatown': 9,
            'Presidio': 14,
            'Fisherman\'s Wharf': 7
        },
        'Chinatown': {
            'Sunset District': 29,
            'Russian Hill': 7,
            'Presidio': 19,
            'Fisherman\'s Wharf': 8
        },
        'Presidio': {
            'Sunset District': 15,
            'Russian Hill': 14,
            'Chinatown': 21,
            'Fisherman\'s Wharf': 19
        },
        'Fisherman\'s Wharf': {
            'Sunset District': 27,
            'Russian Hill': 7,
            'Chinatown': 12,
            'Presidio': 17
        }
    }
    
    friends = [
        {
            'name': 'Michelle',
            'location': 'Chinatown',
            'available_start': '8:15',
            'available_end': '14:00',
            'min_duration': 15
        },
        {
            'name': 'Robert',
            'location': 'Fisherman\'s Wharf',
            'available_start': '9:00',
            'available_end': '13:45',
            'min_duration': 30
        },
        {
            'name': 'George',
            'location': 'Presidio',
            'available_start': '10:30',
            'available_end': '18:45',
            'min_duration': 30
        },
        {
            'name': 'William',
            'location': 'Russian Hill',
            'available_start': '18:30',
            'available_end': '20:45',
            'min_duration': 105
        }
    ]
    
    for friend in friends:
        friend['available_start_min'] = time_to_minutes(friend['available_start'])
        friend['available_end_min'] = time_to_minutes(friend['available_end'])
    
    current_location = 'Sunset District'
    current_time = time_to_minutes('9:00')
    itinerary = []
    
    # Michelle
    friend = friends[0]
    travel_time = travel_times[current_location][friend['location']]
    arrival_time = current_time + travel_time
    start_meeting = max(arrival_time, friend['available_start_min'])
    end_meeting = start_meeting + friend['min_duration']
    if end_meeting > friend['available_end_min']:
        # Skip if cannot meet
        pass
    else:
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start_meeting),
            'end_time': minutes_to_time(end_meeting)
        })
        current_location = friend['location']
        current_time = end_meeting
    
    # Robert
    friend = friends[1]
    travel_time = travel_times[current_location][friend['location']]
    arrival_time = current_time + travel_time
    start_meeting = max(arrival_time, friend['available_start_min'])
    end_meeting = start_meeting + friend['min_duration']
    if end_meeting > friend['available_end_min']:
        # Skip if cannot meet
        pass
    else:
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start_meeting),
            'end_time': minutes_to_time(end_meeting)
        })
        current_location = friend['location']
        current_time = end_meeting
    
    # George
    friend = friends[2]
    travel_time = travel_times[current_location][friend['location']]
    arrival_time = current_time + travel_time
    start_meeting = max(arrival_time, friend['available_start_min'])
    # Calculate latest departure time to meet William
    william_start = friends[3]['available_start_min']
    travel_to_william = travel_times[friend['location']][friends[3]['location']]
    latest_departure = william_start - travel_to_william
    end_meeting = min(latest_departure, friend['available_end_min'])
    if end_meeting < start_meeting + friend['min_duration']:
        # Cannot meet minimum duration
        pass
    else:
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start_meeting),
            'end_time': minutes_to_time(end_meeting)
        })
        current_location = friend['location']
        current_time = end_meeting
    
    # William
    friend = friends[3]
    travel_time = travel_times[current_location][friend['location']]
    arrival_time = current_time + travel_time
    start_meeting = max(arrival_time, friend['available_start_min'])
    end_meeting = start_meeting + friend['min_duration']
    if end_meeting > friend['available_end_min']:
        # Skip if cannot meet
        pass
    else:
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start_meeting),
            'end_time': minutes_to_time(end_meeting)
        })
    
    result = {
        'itinerary': itinerary
    }
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()