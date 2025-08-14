import itertools
import json

def time_str_to_minutes(t_str):
    h, m = map(int, t_str.split(':'))
    return h * 60 + m

def minutes_to_time_str(m):
    h = m // 60
    min = m % 60
    return f"{h}:{min:02d}"

# Define friends with their constraints
friends = [
    {
        'name': 'Laura',
        'location': "The Castro",
        'start': time_str_to_minutes('19:45'),
        'end': time_str_to_minutes('21:30'),
        'duration': 105
    },
    {
        'name': 'Daniel',
        'location': "Golden Gate Park",
        'start': time_str_to_minutes('21:15'),
        'end': time_str_to_minutes('21:45'),
        'duration': 15
    },
    {
        'name': 'William',
        'location': "Embarcadero",
        'start': time_str_to_minutes('7:00'),
        'end': time_str_to_minutes('9:00'),
        'duration': 90
    },
    {
        'name': 'Karen',
        'location': "Russian Hill",
        'start': time_str_to_minutes('14:30'),
        'end': time_str_to_minutes('19:45'),
        'duration': 30
    },
    {
        'name': 'Stephanie',
        'location': "Nob Hill",
        'start': time_str_to_minutes('7:30'),
        'end': time_str_to_minutes('9:30'),
        'duration': 45
    },
    {
        'name': 'Joseph',
        'location': "Alamo Square",
        'start': time_str_to_minutes('11:30'),
        'end': time_str_to_minutes('12:45'),
        'duration': 15
    },
    {
        'name': 'Kimberly',
        'location': "North Beach",
        'start': time_str_to_minutes('15:45'),
        'end': time_str_to_minutes('19:15'),
        'duration': 30
    }
]

# Define travel times between locations
travel_times = {
    "Fisherman's Wharf": {
        "The Castro": 26,
        "Golden Gate Park": 25,
        "Embarcadero": 8,
        "Russian Hill": 7,
        "Nob Hill": 11,
        "Alamo Square": 20,
        "North Beach": 6
    },
    "The Castro": {
        "Fisherman's Wharf": 24,
        "Golden Gate Park": 11,
        "Embarcadero": 22,
        "Russian Hill": 18,
        "Nob Hill": 16,
        "Alamo Square": 8,
        "North Beach": 20
    },
    "Golden Gate Park": {
        "Fisherman's Wharf": 24,
        "The Castro": 13,
        "Embarcadero": 25,
        "Russian Hill": 19,
        "Nob Hill": 20,
        "Alamo Square": 10,
        "North Beach": 24
    },
    "Embarcadero": {
        "Fisherman's Wharf": 6,
        "The Castro": 25,
        "Golden Gate Park": 25,
        "Russian Hill": 8,
        "Nob Hill": 10,
        "Alamo Square": 19,
        "North Beach": 5
    },
    "Russian Hill": {
        "Fisherman's Wharf": 7,
        "The Castro": 21,
        "Golden Gate Park": 21,
        "Embarcadero": 8,
        "Nob Hill": 5,
        "Alamo Square": 15,
        "North Beach": 5
    },
    "Nob Hill": {
        "Fisherman's Wharf": 11,
        "The Castro": 17,
        "Golden Gate Park": 17,
        "Embarcadero": 9,
        "Russian Hill": 5,
        "Alamo Square": 11,
        "North Beach": 8
    },
    "Alamo Square": {
        "Fisherman's Wharf": 19,
        "The Castro": 8,
        "Golden Gate Park": 9,
        "Embarcadero": 17,
        "Russian Hill": 13,
        "Nob Hill": 11,
        "North Beach": 15
    },
    "North Beach": {
        "Fisherman's Wharf": 5,
        "The Castro": 22,
        "Golden Gate Park": 22,
        "Embarcadero": 6,
        "Russian Hill": 4,
        "Nob Hill": 7,
        "Alamo Square": 16
    }
}

best_schedule = []
max_met = 0
start_time = time_str_to_minutes("9:00")

for subset_size in range(len(friends), 0, -1):
    for subset in itertools.combinations(friends, subset_size):
        for perm in itertools.permutations(subset):
            current_time = start_time
            current_location = "Fisherman's Wharf"
            valid = True
            itinerary = []
            for friend in perm:
                travel_time = travel_times[current_location][friend['location']]
                arrival_time = current_time + travel_time
                earliest_start = max(arrival_time, friend['start'])
                if earliest_start + friend['duration'] > friend['end']:
                    valid = False
                    break
                itinerary.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time_str(earliest_start),
                    'end_time': minutes_to_time_str(earliest_start + friend['duration'])
                })
                current_time = earliest_start + friend['duration']
                current_location = friend['location']
            if valid:
                if subset_size > max_met:
                    best_schedule = itinerary
                    max_met = subset_size
                elif subset_size == max_met:
                    pass  # Take the first valid one found
    if max_met == subset_size:
        break

result = {
    "itinerary": best_schedule
}

print(json.dumps(result, indent=2))