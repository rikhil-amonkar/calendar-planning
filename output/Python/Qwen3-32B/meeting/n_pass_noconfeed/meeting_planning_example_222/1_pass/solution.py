import itertools
import json

def time_str_to_min(t_str):
    h, m = map(int, t_str.split(':'))
    return h * 60 + m

def min_to_time_str(m):
    h = m // 60
    mm = m % 60
    return f"{h}:{mm}"

def get_travel_time(from_loc, to_loc):
    travel_times = {
        'Nob Hill': {
            'North Beach': 8,
            "Fisherman's Wharf": 11,
            'Bayview': 19
        },
        'North Beach': {
            'Nob Hill': 7,
            "Fisherman's Wharf": 5,
            'Bayview': 22
        },
        "Fisherman's Wharf": {
            'Nob Hill': 11,
            'North Beach': 6,
            'Bayview': 26
        },
        'Bayview': {
            'Nob Hill': 20,
            'North Beach': 21,
            "Fisherman's Wharf": 25
        }
    }
    return travel_times[from_loc][to_loc]

def simulate_perm(perm):
    current_time = time_str_to_min('9:00')
    current_location = 'Nob Hill'
    itinerary = []
    for friend in perm:
        travel_time = get_travel_time(current_location, friend['location'])
        arrival_time = current_time + travel_time
        available_start = time_str_to_min(friend['available_start'])
        available_end = time_str_to_min(friend['available_end'])
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + friend['min_duration']
        if meeting_end > available_end:
            return None
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': min_to_time_str(meeting_start),
            'end_time': min_to_time_str(meeting_end)
        })
        current_time = meeting_end
        current_location = friend['location']
    return itinerary

friends = [
    {
        'name': 'Helen',
        'location': 'North Beach',
        'available_start': '7:00',
        'available_end': '16:45',
        'min_duration': 120
    },
    {
        'name': 'Kimberly',
        'location': "Fisherman's Wharf",
        'available_start': '16:30',
        'available_end': '21:00',
        'min_duration': 45
    },
    {
        'name': 'Patricia',
        'location': 'Bayview',
        'available_start': '18:00',
        'available_end': '21:15',
        'min_duration': 120
    }
]

best_itinerary = []
best_length = 0

for r in range(1, len(friends) + 1):
    for perm in itertools.permutations(friends, r):
        itinerary = simulate_perm(perm)
        if itinerary is not None:
            if len(itinerary) > best_length:
                best_length = len(itinerary)
                best_itinerary = itinerary

result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))