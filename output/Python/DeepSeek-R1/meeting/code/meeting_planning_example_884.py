import json

def min_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

friends = [
    {
        'name': 'Robert',
        'location': 'Chinatown',
        'start': 7 * 60 + 45,
        'end': 17 * 60 + 30,
        'duration': 120
    },
    {
        'name': 'David',
        'location': 'Sunset District',
        'start': 12 * 60 + 30,
        'end': 19 * 60 + 45,
        'duration': 45
    },
    {
        'name': 'Matthew',
        'location': 'Alamo Square',
        'start': 8 * 60 + 45,
        'end': 13 * 60 + 45,
        'duration': 90
    },
    {
        'name': 'Jessica',
        'location': 'Financial District',
        'start': 9 * 60 + 30,
        'end': 18 * 60 + 45,
        'duration': 45
    },
    {
        'name': 'Melissa',
        'location': 'North Beach',
        'start': 7 * 60 + 15,
        'end': 16 * 60 + 45,
        'duration': 45
    },
    {
        'name': 'Mark',
        'location': 'Embarcadero',
        'start': 15 * 60 + 15,
        'end': 17 * 60 + 0,
        'duration': 45
    },
    {
        'name': 'Deborah',
        'location': 'Presidio',
        'start': 19 * 60 + 0,
        'end': 19 * 60 + 45,
        'duration': 45
    },
    {
        'name': 'Karen',
        'location': 'Golden Gate Park',
        'start': 19 * 60 + 30,
        'end': 22 * 60 + 0,
        'duration': 120
    },
    {
        'name': 'Laura',
        'location': 'Bayview',
        'start': 21 * 60 + 15,
        'end': 22 * 60 + 15,
        'duration': 15
    },
]

travel_times = {
    ('Richmond District', 'Chinatown'): 20,
    ('Richmond District', 'Sunset District'): 11,
    ('Richmond District', 'Alamo Square'): 13,
    ('Richmond District', 'Financial District'): 22,
    ('Richmond District', 'North Beach'): 17,
    ('Richmond District', 'Embarcadero'): 19,
    ('Richmond District', 'Presidio'): 7,
    ('Richmond District', 'Golden Gate Park'): 9,
    ('Richmond District', 'Bayview'): 27,
    ('Chinatown', 'Richmond District'): 20,
    ('Chinatown', 'Sunset District'): 29,
    ('Chinatown', 'Alamo Square'): 17,
    ('Chinatown', 'Financial District'): 5,
    ('Chinatown', 'North Beach'): 3,
    ('Chinatown', 'Embarcadero'): 5,
    ('Chinatown', 'Presidio'): 19,
    ('Chinatown', 'Golden Gate Park'): 23,
    ('Chinatown', 'Bayview'): 20,
    ('Sunset District', 'Richmond District'): 12,
    ('Sunset District', 'Chinatown'): 30,
    ('Sunset District', 'Alamo Square'): 17,
    ('Sunset District', 'Financial District'): 30,
    ('Sunset District', 'North Beach'): 28,
    ('Sunset District', 'Embarcadero'): 30,
    ('Sunset District', 'Presidio'): 16,
    ('Sunset District', 'Golden Gate Park'): 11,
    ('Sunset District', 'Bayview'): 22,
    ('Alamo Square', 'Richmond District'): 11,
    ('Alamo Square', 'Chinatown'): 15,
    ('Alamo Square', 'Sunset District'): 16,
    ('Alamo Square', 'Financial District'): 17,
    ('Alamo Square', 'North Beach'): 15,
    ('Alamo Square', 'Embarcadero'): 16,
    ('Alamo Square', 'Presidio'): 17,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Bayview'): 16,
    ('Financial District', 'Richmond District'): 21,
    ('Financial District', 'Chinatown'): 5,
    ('Financial District', 'Sunset District'): 30,
    ('Financial District', 'Alamo Square'): 17,
    ('Financial District', 'North Beach'): 7,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Presidio'): 22,
    ('Financial District', 'Golden Gate Park'): 23,
    ('Financial District', 'Bayview'): 19,
    ('North Beach', 'Richmond District'): 18,
    ('North Beach', 'Chinatown'): 6,
    ('North Beach', 'Sunset District'): 27,
    ('North Beach', 'Alamo Square'): 16,
    ('North Beach', 'Financial District'): 8,
    ('North Beach', 'Embarcadero'): 6,
    ('North Beach', 'Presidio'): 17,
    ('North Beach', 'Golden Gate Park'): 22,
    ('North Beach', 'Bayview'): 25,
    ('Embarcadero', 'Richmond District'): 21,
    ('Embarcadero', 'Chinatown'): 7,
    ('Embarcadero', 'Sunset District'): 30,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'North Beach'): 5,
    ('Embarcadero', 'Presidio'): 20,
    ('Embarcadero', 'Golden Gate Park'): 25,
    ('Embarcadero', 'Bayview'): 21,
    ('Presidio', 'Richmond District'): 7,
    ('Presidio', 'Chinatown'): 21,
    ('Presidio', 'Sunset District'): 15,
    ('Presidio', 'Alamo Square'): 19,
    ('Presidio', 'Financial District'): 23,
    ('Presidio', 'North Beach'): 18,
    ('Presidio', 'Embarcadero'): 20,
    ('Presidio', 'Golden Gate Park'): 12,
    ('Presidio', 'Bayview'): 31,
    ('Golden Gate Park', 'Richmond District'): 7,
    ('Golden Gate Park', 'Chinatown'): 23,
    ('Golden Gate Park', 'Sunset District'): 10,
    ('Golden Gate Park', 'Alamo Square'): 9,
    ('Golden Gate Park', 'Financial District'): 26,
    ('Golden Gate Park', 'North Beach'): 23,
    ('Golden Gate Park', 'Embarcadero'): 25,
    ('Golden Gate Park', 'Presidio'): 11,
    ('Golden Gate Park', 'Bayview'): 23,
    ('Bayview', 'Richmond District'): 25,
    ('Bayview', 'Chinatown'): 19,
    ('Bayview', 'Sunset District'): 23,
    ('Bayview', 'Alamo Square'): 16,
    ('Bayview', 'Financial District'): 19,
    ('Bayview', 'North Beach'): 22,
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', 'Presidio'): 32,
    ('Bayview', 'Golden Gate Park'): 22,
}

current_time = 540  # 9:00 AM
current_location = 'Richmond District'
itinerary = []
remaining_friends = friends.copy()

while True:
    feasible = []
    for friend in remaining_friends:
        to_loc = friend['location']
        key = (current_location, to_loc)
        if key not in travel_times:
            continue
        travel_time = travel_times[key]
        earliest_start = max(friend['start'], current_time + travel_time)
        latest_start = friend['end'] - friend['duration']
        if earliest_start > latest_start:
            continue
        end_time = earliest_start + friend['duration']
        feasible.append((end_time, earliest_start, friend))
    if not feasible:
        break
    feasible.sort()
    selected = feasible[0]
    end_time, start_time, friend = selected
    itinerary.append({
        "action": "meet",
        "location": friend['location'],
        "person": friend['name'],
        "start_time": min_to_time(start_time),
        "end_time": min_to_time(end_time)
    })
    current_time = end_time
    current_location = friend['location']
    remaining_friends = [f for f in remaining_friends if f['name'] != friend['name']]

output = {"itinerary": itinerary}
print(json.dumps(output, indent=2))