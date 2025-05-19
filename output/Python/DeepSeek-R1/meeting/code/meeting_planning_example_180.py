import itertools
import json

def time_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02}"

travel_times = {
    'North Beach': {'Mission District': 18, 'The Castro': 22},
    'Mission District': {'North Beach': 17, 'The Castro': 7},
    'The Castro': {'North Beach': 20, 'Mission District': 7}
}

friends = [
    {
        'name': 'James',
        'location': 'Mission District',
        'available_start': 12 * 60 +45,
        'available_end': 14 * 60,
        'min_duration': 75
    },
    {
        'name': 'Robert',
        'location': 'The Castro',
        'available_start': 12 * 60 +45,
        'available_end': 15 * 60 +15,
        'min_duration': 30
    }
]

start_time = 9 * 60
start_location = 'North Beach'

best_itinerary = []
max_met = 0

for perm in itertools.permutations(friends):
    current_location = start_location
    current_time = start_time
    itinerary = []
    met = 0
    
    for friend in perm:
        travel_time = travel_times[current_location].get(friend['location'])
        if travel_time is None:
            break
        
        arrival_time = max(current_time + travel_time, friend['available_start'])
        latest_start = friend['available_end'] - friend['min_duration']
        
        if arrival_time > latest_start:
            break
        
        meeting_start = arrival_time
        meeting_end = friend['available_end']
        
        itinerary.append({
            'action': 'meet',
            'location': friend['location'],
            'person': friend['name'],
            'start_time': time_to_str(meeting_start),
            'end_time': time_to_str(meeting_end)
        })
        current_time = meeting_end
        current_location = friend['location']
        met += 1
    
    if met > max_met or (met == max_met and len(itinerary) > len(best_itinerary)):
        best_itinerary = itinerary
        max_met = met

print(json.dumps({'itinerary': best_itinerary}, indent=2))