import itertools
import json

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

travel_time = {
    ('Bayview', 'Embarcadero'): 19,
    ('Bayview', "Fisherman's Wharf"): 25,
    ('Bayview', 'Financial District'): 19,
    ('Embarcadero', 'Bayview'): 21,
    ('Embarcadero', "Fisherman's Wharf"): 6,
    ('Embarcadero', 'Financial District'): 5,
    ("Fisherman's Wharf", 'Bayview'): 26,
    ("Fisherman's Wharf", 'Embarcadero'): 8,
    ("Fisherman's Wharf", 'Financial District'): 11,
    ('Financial District', 'Bayview'): 19,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', "Fisherman's Wharf"): 10,
}

friends = [
    {
        'name': 'Karen',
        'location': "Fisherman's Wharf",
        'available_start': time_to_minutes("8:45"),
        'available_end': time_to_minutes("15:00"),
        'required_duration': 30
    },
    {
        'name': 'Anthony',
        'location': "Financial District",
        'available_start': time_to_minutes("9:15"),
        'available_end': time_to_minutes("21:30"),
        'required_duration': 105
    },
    {
        'name': 'Betty',
        'location': "Embarcadero",
        'available_start': time_to_minutes("19:45"),
        'available_end': time_to_minutes("21:45"),
        'required_duration': 15
    }
]

best_itinerary = []
max_friends = 0

for perm in itertools.permutations(friends):
    current_time = time_to_minutes("9:00")
    current_location = 'Bayview'
    itinerary = []
    valid = True

    for friend in perm:
        from_loc = current_location
        to_loc = friend['location']
        travel_duration = travel_time.get((from_loc, to_loc))
        if travel_duration is None:
            valid = False
            break
        current_time += travel_duration

        if current_time > friend['available_end']:
            valid = False
            break

        start_meet = max(current_time, friend['available_start'])
        end_meet = start_meet + friend['required_duration']

        if end_meet > friend['available_end']:
            valid = False
            break

        itinerary.append({
            'action': 'meet',
            'location': to_loc,
            'person': friend['name'],
            'start_time': minutes_to_time(start_meet),
            'end_time': minutes_to_time(end_meet)
        })

        current_time = end_meet
        current_location = to_loc

    if valid and len(itinerary) > max_friends:
        max_friends = len(itinerary)
        best_itinerary = itinerary

result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))