import json
from itertools import permutations

# Travel times dictionary: travel_times[from][to] = minutes
travel_times = {
    'Embarcadero': {
        'Bayview': 21, 'Chinatown': 7, 'Alamo Square': 19, 'Nob Hill': 10, 'Presidio': 20,
        'Union Square': 10, 'The Castro': 25, 'North Beach': 5, 'Fisherman\'s Wharf': 6, 'Marina District': 12
    },
    'Bayview': {
        'Embarcadero': 19, 'Chinatown': 19, 'Alamo Square': 16, 'Nob Hill': 20, 'Presidio': 32,
        'Union Square': 18, 'The Castro': 19, 'North Beach': 22, 'Fisherman\'s Wharf': 25, 'Marina District': 27
    },
    'Chinatown': {
        'Embarcadero': 5, 'Bayview': 20, 'Alamo Square': 17, 'Nob Hill': 9, 'Presidio': 19,
        'Union Square': 7, 'The Castro': 22, 'North Beach': 3, 'Fisherman\'s Wharf': 8, 'Marina District': 12
    },
    'Alamo Square': {
        'Embarcadero': 16, 'Bayview': 16, 'Chinatown': 15, 'Nob Hill': 11, 'Presidio': 17,
        'Union Square': 14, 'The Castro': 8, 'North Beach': 15, 'Fisherman\'s Wharf': 19, 'Marina District': 15
    },
    'Nob Hill': {
        'Embarcadero': 9, 'Bayview': 19, 'Chinatown': 6, 'Alamo Square': 11, 'Presidio': 17,
        'Union Square': 7, 'The Castro': 17, 'North Beach': 8, 'Fisherman\'s Wharf': 10, 'Marina District': 11
    },
    'Presidio': {
        'Embarcadero': 20, 'Bayview': 31, 'Chinatown': 21, 'Alamo Square': 19, 'Nob Hill': 18,
        'Union Square': 22, 'The Castro': 21, 'North Beach': 18, 'Fisherman\'s Wharf': 19, 'Marina District': 11
    },
    'Union Square': {
        'Embarcadero': 11, 'Bayview': 15, 'Chinatown': 7, 'Alamo Square': 15, 'Nob Hill': 9,
        'Presidio': 24, 'The Castro': 17, 'North Beach': 10, 'Fisherman\'s Wharf': 15, 'Marina District': 18
    },
    'The Castro': {
        'Embarcadero': 22, 'Bayview': 19, 'Chinatown': 22, 'Alamo Square': 8, 'Nob Hill': 16,
        'Presidio': 20, 'Union Square': 19, 'North Beach': 20, 'Fisherman\'s Wharf': 24, 'Marina District': 21
    },
    'North Beach': {
        'Embarcadero': 6, 'Bayview': 25, 'Chinatown': 6, 'Alamo Square': 16, 'Nob Hill': 7,
        'Presidio': 17, 'Union Square': 7, 'The Castro': 23, 'Fisherman\'s Wharf': 5, 'Marina District': 9
    },
    'Fisherman\'s Wharf': {
        'Embarcadero': 8, 'Bayview': 26, 'Chinatown': 12, 'Alamo Square': 21, 'Nob Hill': 11,
        'Presidio': 17, 'Union Square': 13, 'The Castro': 27, 'North Beach': 6, 'Marina District': 9
    },
    'Marina District': {
        'Embarcadero': 14, 'Bayview': 27, 'Chinatown': 15, 'Alamo Square': 15, 'Nob Hill': 12,
        'Presidio': 10, 'Union Square': 16, 'The Castro': 22, 'North Beach': 11, 'Fisherman\'s Wharf': 10
    }
}

# Friend constraints
friends = [
    {'name': 'Matthew', 'location': 'Bayview', 'start': '19:15', 'end': '22:00', 'min_duration': 120},
    {'name': 'Karen', 'location': 'Chinatown', 'start': '19:15', 'end': '21:15', 'min_duration': 90},
    {'name': 'Sarah', 'location': 'Alamo Square', 'start': '20:00', 'end': '21:45', 'min_duration': 105},
    {'name': 'Jessica', 'location': 'Nob Hill', 'start': '16:30', 'end': '18:45', 'min_duration': 120},
    {'name': 'Stephanie', 'location': 'Presidio', 'start': '7:30', 'end': '10:15', 'min_duration': 60},
    {'name': 'Mary', 'location': 'Union Square', 'start': '16:45', 'end': '21:30', 'min_duration': 60},
    {'name': 'Charles', 'location': 'The Castro', 'start': '16:30', 'end': '22:00', 'min_duration': 105},
    {'name': 'Nancy', 'location': 'North Beach', 'start': '14:45', 'end': '20:00', 'min_duration': 15},
    {'name': 'Thomas', 'location': 'Fisherman\'s Wharf', 'start': '13:30', 'end': '19:00', 'min_duration': 30},
    {'name': 'Brian', 'location': 'Marina District', 'start': '12:15', 'end': '18:00', 'min_duration': 60}
]

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def get_available_slots(friend, current_time):
    friend_start = time_to_minutes(friend['start'])
    friend_end = time_to_minutes(friend['end'])
    min_duration = friend['min_duration']
    
    latest_start = friend_end - min_duration
    available_start = max(current_time, friend_start)
    
    if available_start > latest_start:
        return None
    
    return {
        'start': available_start,
        'end': min(available_start + min_duration, friend_end)
    }

def calculate_schedule():
    current_location = 'Embarcadero'
    current_time = time_to_minutes('9:00')
    itinerary = []
    remaining_friends = friends.copy()
    
    # Try to meet Stephanie first since she's available early
    stephanie = next(f for f in remaining_friends if f['name'] == 'Stephanie')
    if current_time <= time_to_minutes(stephanie['end']):
        travel_time = travel_times[current_location][stephanie['location']]
        arrival_time = current_time + travel_time
        slot = get_available_slots(stephanie, arrival_time)
        if slot:
            itinerary.append({
                'action': 'meet',
                'location': stephanie['location'],
                'person': stephanie['name'],
                'start_time': minutes_to_time(slot['start']),
                'end_time': minutes_to_time(slot['end'])
            })
            current_location = stephanie['location']
            current_time = slot['end']
            remaining_friends.remove(stephanie)
    
    # Sort remaining friends by earliest availability
    remaining_friends.sort(key=lambda x: time_to_minutes(x['start']))
    
    for friend in remaining_friends:
        travel_time = travel_times[current_location][friend['location']]
        arrival_time = current_time + travel_time
        slot = get_available_slots(friend, arrival_time)
        if slot:
            itinerary.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': minutes_to_time(slot['start']),
                'end_time': minutes_to_time(slot['end'])
            })
            current_location = friend['location']
            current_time = slot['end']
    
    return itinerary

def main():
    itinerary = calculate_schedule()
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()