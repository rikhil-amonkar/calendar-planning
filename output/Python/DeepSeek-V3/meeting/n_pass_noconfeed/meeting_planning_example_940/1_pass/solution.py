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
    # Travel times dictionary: {from_location: {to_location: minutes}}
    travel_times = {
        'Union Square': {
            'Mission District': 14, 'Fisherman\'s Wharf': 15, 'Russian Hill': 13,
            'Marina District': 18, 'North Beach': 10, 'Chinatown': 7, 'Pacific Heights': 15,
            'The Castro': 17, 'Nob Hill': 9, 'Sunset District': 27
        },
        'Mission District': {
            'Union Square': 15, 'Fisherman\'s Wharf': 22, 'Russian Hill': 15,
            'Marina District': 19, 'North Beach': 17, 'Chinatown': 16, 'Pacific Heights': 16,
            'The Castro': 7, 'Nob Hill': 12, 'Sunset District': 24
        },
        'Fisherman\'s Wharf': {
            'Union Square': 13, 'Mission District': 22, 'Russian Hill': 7,
            'Marina District': 9, 'North Beach': 6, 'Chinatown': 12, 'Pacific Heights': 12,
            'The Castro': 27, 'Nob Hill': 11, 'Sunset District': 27
        },
        'Russian Hill': {
            'Union Square': 10, 'Mission District': 16, 'Fisherman\'s Wharf': 7,
            'Marina District': 7, 'North Beach': 5, 'Chinatown': 9, 'Pacific Heights': 7,
            'The Castro': 21, 'Nob Hill': 5, 'Sunset District': 23
        },
        'Marina District': {
            'Union Square': 16, 'Mission District': 20, 'Fisherman\'s Wharf': 10,
            'Russian Hill': 8, 'North Beach': 11, 'Chinatown': 15, 'Pacific Heights': 7,
            'The Castro': 22, 'Nob Hill': 12, 'Sunset District': 19
        },
        'North Beach': {
            'Union Square': 7, 'Mission District': 18, 'Fisherman\'s Wharf': 5,
            'Russian Hill': 4, 'Marina District': 9, 'Chinatown': 6, 'Pacific Heights': 8,
            'The Castro': 23, 'Nob Hill': 7, 'Sunset District': 27
        },
        'Chinatown': {
            'Union Square': 7, 'Mission District': 17, 'Fisherman\'s Wharf': 8,
            'Russian Hill': 7, 'Marina District': 12, 'North Beach': 3, 'Pacific Heights': 10,
            'The Castro': 22, 'Nob Hill': 9, 'Sunset District': 29
        },
        'Pacific Heights': {
            'Union Square': 12, 'Mission District': 15, 'Fisherman\'s Wharf': 13,
            'Russian Hill': 7, 'Marina District': 6, 'North Beach': 9, 'Chinatown': 11,
            'The Castro': 16, 'Nob Hill': 8, 'Sunset District': 21
        },
        'The Castro': {
            'Union Square': 19, 'Mission District': 7, 'Fisherman\'s Wharf': 24,
            'Russian Hill': 18, 'Marina District': 21, 'North Beach': 20, 'Chinatown': 22,
            'Pacific Heights': 16, 'Nob Hill': 16, 'Sunset District': 17
        },
        'Nob Hill': {
            'Union Square': 7, 'Mission District': 13, 'Fisherman\'s Wharf': 10,
            'Russian Hill': 5, 'Marina District': 11, 'North Beach': 8, 'Chinatown': 6,
            'Pacific Heights': 8, 'The Castro': 17, 'Sunset District': 24
        },
        'Sunset District': {
            'Union Square': 30, 'Mission District': 25, 'Fisherman\'s Wharf': 29,
            'Russian Hill': 24, 'Marina District': 21, 'North Beach': 28, 'Chinatown': 30,
            'Pacific Heights': 21, 'The Castro': 17, 'Nob Hill': 27
        }
    }

    # Fix typo in Marina District
    travel_times['Marina District'] = travel_times.pop('Marina District')

    # Friend constraints: {name: (location, available_start, available_end, min_duration)}
    friends = {
        'Kevin': ('Mission District', '20:45', '21:45', 60),
        'Mark': ('Fisherman\'s Wharf', '17:15', '20:00', 90),
        'Jessica': ('Russian Hill', '9:00', '15:00', 120),
        'Jason': ('Marina District', '15:15', '21:45', 120),
        'John': ('North Beach', '9:45', '18:00', 15),
        'Karen': ('Chinatown', '16:45', '19:00', 75),
        'Sarah': ('Pacific Heights', '17:30', '18:15', 45),
        'Amanda': ('The Castro', '20:00', '21:15', 60),
        'Nancy': ('Nob Hill', '9:45', '13:00', 45),
        'Rebecca': ('Sunset District', '8:45', '15:00', 75)
    }

    current_location = 'Union Square'
    current_time = time_to_minutes('9:00')
    itinerary = []

    # Prioritize friends with tighter time windows first
    priority_order = ['Nancy', 'Jessica', 'Rebecca', 'John', 'Jason', 'Karen', 'Sarah', 'Mark', 'Amanda', 'Kevin']
    remaining_friends = set(priority_order)
    scheduled_friends = set()

    while remaining_friends:
        best_friend = None
        best_start = None
        best_end = None
        best_travel_time = float('inf')

        for friend in remaining_friends:
            location, avail_start, avail_end, min_duration = friends[friend]
            avail_start_min = time_to_minutes(avail_start)
            avail_end_min = time_to_minutes(avail_end)
            
            # Calculate earliest possible start time (current time + travel)
            travel_time = travel_times[current_location].get(location, float('inf'))
            earliest_start = current_time + travel_time
            
            # Can't start before friend's availability
            actual_start = max(earliest_start, avail_start_min)
            actual_end = actual_start + min_duration
            
            # Check if fits in friend's window
            if actual_end <= avail_end_min:
                # Prefer friend with earliest possible start time
                if actual_start < best_start if best_start else True:
                    best_friend = friend
                    best_start = actual_start
                    best_end = actual_end
                    best_travel_time = travel_time

        if best_friend:
            location, _, _, _ = friends[best_friend]
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": best_friend,
                "start_time": minutes_to_time(best_start),
                "end_time": minutes_to_time(best_end)
            })
            current_location = location
            current_time = best_end
            scheduled_friends.add(best_friend)
            remaining_friends.remove(best_friend)
        else:
            # No more friends can be scheduled
            break

    return {"itinerary": itinerary}

result = calculate_schedule()
print(json.dumps(result, indent=2))