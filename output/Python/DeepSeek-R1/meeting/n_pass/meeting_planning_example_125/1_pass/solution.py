import json

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

travel_times = {
    ('Embarcadero', 'Financial District'): 5,
    ('Embarcadero', 'Alamo Square'): 19,
    ('Financial District', 'Embarcadero'): 4,
    ('Financial District', 'Alamo Square'): 17,
    ('Alamo Square', 'Embarcadero'): 17,
    ('Alamo Square', 'Financial District'): 17
}

people = [
    {
        'name': 'Stephanie',
        'location': 'Financial District',
        'available_start': 8*60+15,
        'available_end': 11*60+30,
        'min_duration': 90
    },
    {
        'name': 'John',
        'location': 'Alamo Square',
        'available_start': 10*60+15,
        'available_end': 20*60+45,
        'min_duration': 30
    }
]

start_time_minutes = 9 * 60
start_location = 'Embarcadero'

orders = [[0, 1], [1, 0]]
best_itinerary = None
best_finish = float('inf')

for order in orders:
    current_time = start_time_minutes
    current_location = start_location
    itinerary = []
    feasible = True
    for idx in order:
        p = people[idx]
        key = (current_location, p['location'])
        if key not in travel_times:
            feasible = False
            break
        travel_duration = travel_times[key]
        current_time += travel_duration
        meeting_start = max(current_time, p['available_start'])
        meeting_end = meeting_start + p['min_duration']
        if meeting_end > p['available_end']:
            feasible = False
            break
        itinerary.append({
            'action': 'meet',
            'location': p['location'],
            'person': p['name'],
            'start_time': meeting_start,
            'end_time': meeting_end
        })
        current_location = p['location']
        current_time = meeting_end
    if feasible and current_time < best_finish:
        best_finish = current_time
        best_itinerary = itinerary

if best_itinerary is None:
    best_one_itinerary = None
    best_one_finish = float('inf')
    for idx in range(len(people)):
        p = people[idx]
        key = (start_location, p['location'])
        if key not in travel_times:
            continue
        travel_duration = travel_times[key]
        current_time = start_time_minutes + travel_duration
        meeting_start = max(current_time, p['available_start'])
        meeting_end = meeting_start + p['min_duration']
        if meeting_end > p['available_end']:
            continue
        if meeting_end < best_one_finish:
            best_one_finish = meeting_end
            best_one_itinerary = [{
                'action': 'meet',
                'location': p['location'],
                'person': p['name'],
                'start_time': meeting_start,
                'end_time': meeting_end
            }]
    if best_one_itinerary is not None:
        best_itinerary = best_one_itinerary
    else:
        best_itinerary = []

result_itinerary = []
for event in best_itinerary:
    result_itinerary.append({
        "action": event['action'],
        "location": event['location'],
        "person": event['person'],
        "start_time": format_time(event['start_time']),
        "end_time": format_time(event['end_time'])
    })

print(json.dumps({"itinerary": result_itinerary}))