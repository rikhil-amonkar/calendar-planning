import itertools
import json

def minutes_to_time(m):
    h = m // 60
    min = m % 60
    return f"{h}:{min:02d}"

travel_times = {
    ('Bayview', 'Pacific Heights'): 23,
    ('Bayview', 'Mission District'):13,
    ('Bayview', 'Haight-Ashbury'):19,
    ('Bayview', 'Financial District'):19,
    ('Pacific Heights', 'Bayview'):22,
    ('Pacific Heights', 'Mission District'):15,
    ('Pacific Heights', 'Haight-Ashbury'):11,
    ('Pacific Heights', 'Financial District'):13,
    ('Mission District', 'Bayview'):15,
    ('Mission District', 'Pacific Heights'):16,
    ('Mission District', 'Haight-Ashbury'):12,
    ('Mission District', 'Financial District'):17,
    ('Haight-Ashbury', 'Bayview'):18,
    ('Haight-Ashbury', 'Pacific Heights'):12,
    ('Haight-Ashbury', 'Mission District'):11,
    ('Haight-Ashbury', 'Financial District'):21,
    ('Financial District', 'Bayview'):19,
    ('Financial District', 'Pacific Heights'):13,
    ('Financial District', 'Mission District'):17,
    ('Financial District', 'Haight-Ashbury'):19,
}

friends = [
    {'name': 'Mary', 'location': 'Pacific Heights', 'start': 10*60, 'end':19*60, 'duration':45},
    {'name': 'Betty', 'location': 'Haight-Ashbury', 'start':7*60+15, 'end':17*60+15, 'duration':90},
    {'name': 'Charles', 'location': 'Financial District', 'start':11*60+15, 'end':15*60, 'duration':120},
    {'name': 'Lisa', 'location': 'Mission District', 'start':20*60+30, 'end':22*60, 'duration':75},
]

core_friends = [f for f in friends if f['name'] != 'Lisa']
lisa = [f for f in friends if f['name'] == 'Lisa'][0]

best_itinerary = None

for perm in itertools.permutations(core_friends):
    current_location = 'Bayview'
    current_time = 9 * 60
    itinerary = []
    possible = True
    
    for friend in perm:
        key = (current_location, friend['location'])
        if key not in travel_times:
            possible = False
            break
        travel = travel_times[key]
        arrival = current_time + travel
        start = max(arrival, friend['start'])
        end = start + friend['duration']
        if end > friend['end']:
            possible = False
            break
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': minutes_to_time(start),
            'end_time': minutes_to_time(end),
        })
        current_location = friend['location']
        current_time = end
    
    if possible:
        key = (current_location, lisa['location'])
        if key not in travel_times:
            continue
        travel = travel_times[key]
        arrival = current_time + travel
        start = max(arrival, lisa['start'])
        end = start + lisa['duration']
        if end > lisa['end']:
            continue
        itinerary.append({
            'action': 'meet',
            'location': lisa['location'],
            'person': lisa['name'],
            'start_time': minutes_to_time(start),
            'end_time': minutes_to_time(end),
        })
        if best_itinerary is None or len(itinerary) > len(best_itinerary):
            best_itinerary = itinerary.copy()
        if len(best_itinerary) == 4:
            break

output = {"itinerary": best_itinerary} if best_itinerary else {"itinerary": []}
print(json.dumps(output, indent=2))