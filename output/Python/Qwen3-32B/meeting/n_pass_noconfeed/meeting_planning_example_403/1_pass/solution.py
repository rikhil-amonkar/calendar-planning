import itertools
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def simulate(permutation, travel_time, start_time=540, start_location='Union Square'):
    current_time = start_time
    current_location = start_location
    itinerary = []
    for friend in permutation:
        travel_duration = travel_time[current_location][friend['location']]
        arrival_time = current_time + travel_duration
        start_time_meeting = max(arrival_time, friend['available_start'])
        end_time_meeting = start_time_meeting + friend['required_duration']
        if end_time_meeting > friend['available_end']:
            return None
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start_time_meeting),
            'end_time': minutes_to_time(end_time_meeting)
        })
        current_time = end_time_meeting
        current_location = friend['location']
    return itinerary

def main():
    travel_time = {
        'Union Square': {
            'Union Square': 0,
            'Golden Gate Park': 22,
            'Pacific Heights': 15,
            'Presidio': 24,
            'Chinatown': 7,
            'The Castro': 19
        },
        'Golden Gate Park': {
            'Union Square': 22,
            'Golden Gate Park': 0,
            'Pacific Heights': 16,
            'Presidio': 11,
            'Chinatown': 23,
            'The Castro': 13
        },
        'Pacific Heights': {
            'Union Square': 12,
            'Golden Gate Park': 15,
            'Pacific Heights': 0,
            'Presidio': 11,
            'Chinatown': 11,
            'The Castro': 16
        },
        'Presidio': {
            'Union Square': 22,
            'Golden Gate Park': 12,
            'Pacific Heights': 11,
            'Presidio': 0,
            'Chinatown': 21,
            'The Castro': 21
        },
        'Chinatown': {
            'Union Square': 7,
            'Golden Gate Park': 23,
            'Pacific Heights': 10,
            'Presidio': 19,
            'Chinatown': 0,
            'The Castro': 22
        },
        'The Castro': {
            'Union Square': 19,
            'Golden Gate Park': 11,
            'Pacific Heights': 16,
            'Presidio': 20,
            'Chinatown': 20,
            'The Castro': 0
        }
    }

    friends = [
        {
            'name': 'Rebecca',
            'location': 'Chinatown',
            'available_start': 9*60 +45, 
            'available_end': 21*60 +30, 
            'required_duration': 90
        },
        {
            'name': 'Robert',
            'location': 'The Castro',
            'available_start': 8*60 +30, 
            'available_end': 14*60 +15, 
            'required_duration': 30
        },
        {
            'name': 'Andrew',
            'location': 'Golden Gate Park',
            'available_start': 11*60 +45, 
            'available_end': 14*60 +30, 
            'required_duration': 75
        },
        {
            'name': 'Sarah',
            'location': 'Pacific Heights',
            'available_start': 16*60 +15, 
            'available_end': 18*60 +45, 
            'required_duration': 15
        },
        {
            'name': 'Nancy',
            'location': 'Presidio',
            'available_start': 17*60 +30, 
            'available_end': 19*60 +15, 
            'required_duration': 60
        }
    ]

    best_itinerary = None
    for k in range(len(friends), 0, -1):
        for perm in itertools.permutations(friends, k):
            itinerary = simulate(perm, travel_time)
            if itinerary is not None:
                best_itinerary = itinerary
                break
        if best_itinerary is not None:
            break

    print(json.dumps({"itinerary": best_itinerary}))

if __name__ == "__main__":
    main()