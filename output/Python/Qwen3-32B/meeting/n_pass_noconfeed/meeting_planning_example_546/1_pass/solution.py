import itertools
import json
from datetime import datetime

def time_str_to_minutes(time_str):
    return datetime.strptime(time_str, '%I:%M%p').hour * 60 + datetime.strptime(time_str, '%I:%M%p').minute

def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    # Embarcadero
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Union Square'): 10,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Pacific Heights'): 11,
    ('Embarcadero', 'Nob Hill'): 10,
    ('Embarcadero', 'Bayview'): 21,
    # Richmond District
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Union Square'): 21,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'Pacific Heights'): 10,
    ('Richmond District', 'Nob Hill'): 17,
    ('Richmond District', 'Bayview'): 26,
    # Union Square
    ('Union Square', 'Embarcadero'): 11,
    ('Union Square', 'Richmond District'): 20,
    ('Union Square', 'Financial District'): 9,
    ('Union Square', 'Pacific Heights'): 15,
    ('Union Square', 'Nob Hill'): 9,
    ('Union Square', 'Bayview'): 15,
    # Financial District
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Union Square'): 9,
    ('Financial District', 'Pacific Heights'): 13,
    ('Financial District', 'Nob Hill'): 8,
    ('Financial District', 'Bayview'): 19,
    # Pacific Heights
    ('Pacific Heights', 'Embarcadero'): 10,
    ('Pacific Heights', 'Richmond District'): 12,
    ('Pacific Heights', 'Union Square'): 12,
    ('Pacific Heights', 'Financial District'): 13,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Bayview'): 22,
    # Nob Hill
    ('Nob Hill', 'Embarcadero'): 9,
    ('Nob Hill', 'Richmond District'): 14,
    ('Nob Hill', 'Union Square'): 7,
    ('Nob Hill', 'Financial District'): 9,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Nob Hill', 'Bayview'): 19,
    # Bayview
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Union Square'): 17,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Nob Hill'): 20,
}

friends = [
    {
        'name': 'Nancy',
        'location': 'Pacific Heights',
        'available_start': '8:00AM',
        'available_end': '11:30AM',
        'min_duration': 90
    },
    {
        'name': 'Lisa',
        'location': 'Union Square',
        'available_start': '9:00AM',
        'available_end': '4:30PM',
        'min_duration': 45
    },
    {
        'name': 'Joshua',
        'location': 'Financial District',
        'available_start': '12:00PM',
        'available_end': '3:15PM',
        'min_duration': 15
    },
    {
        'name': 'Andrew',
        'location': 'Nob Hill',
        'available_start': '11:30AM',
        'available_end': '8:15PM',
        'min_duration': 60
    },
    {
        'name': 'John',
        'location': 'Bayview',
        'available_start': '4:45PM',
        'available_end': '9:30PM',
        'min_duration': 75
    },
    {
        'name': 'Kenneth',
        'location': 'Richmond District',
        'available_start': '9:15PM',
        'available_end': '10:00PM',
        'min_duration': 30
    }
]

best_itinerary = []
max_met = 0

for perm in itertools.permutations(friends):
    current_time = time_str_to_minutes('9:00AM')
    current_location = 'Embarcadero'
    itinerary = []
    met = 0
    for friend in perm:
        travel_key = (current_location, friend['location'])
        if travel_key not in travel_times:
            break
        travel_time = travel_times[travel_key]
        arrival_time = current_time + travel_time
        
        available_start = time_str_to_minutes(friend['available_start'])
        available_end = time_str_to_minutes(friend['available_end'])
        min_duration = friend['min_duration']
        
        start_candidate = max(arrival_time, available_start)
        end_candidate = start_candidate + min_duration
        
        if end_candidate > available_end:
            break
        
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time_str(start_candidate),
            'end_time': minutes_to_time_str(end_candidate)
        })
        met += 1
        current_time = end_candidate
        current_location = friend['location']
    
    if met > max_met:
        max_met = met
        best_itinerary = itinerary

result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))