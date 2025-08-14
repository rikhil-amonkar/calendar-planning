import itertools
import json

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    'North Beach': {'Mission District': 18, 'The Castro': 22},
    'Mission District': {'North Beach': 17, 'The Castro': 7},
    'The Castro': {'North Beach': 20, 'Mission District': 7}
}

friends = [
    {
        'name': 'James',
        'location': 'Mission District',
        'available_start': 765,  # 12:45 PM
        'available_end': 840,    # 2:00 PM
        'required_duration': 75
    },
    {
        'name': 'Robert',
        'location': 'The Castro',
        'available_start': 765,  # 12:45 PM
        'available_end': 915,    # 3:15 PM
        'required_duration': 30
    }
]

start_location = 'North Beach'
start_time = 9 * 60  # 9:00 AM in minutes

best_itinerary = None

for perm in itertools.permutations(friends):
    current_time = start_time
    current_location = start_location
    itinerary = []
    valid = True
    
    for friend in perm:
        dest = friend['location']
        travel_time = travel_times[current_location][dest]
        current_time += travel_time
        
        meeting_start = max(current_time, friend['available_start'])
        meeting_end = meeting_start + friend['required_duration']
        
        if meeting_end > friend['available_end']:
            valid = False
            break
            
        itinerary.append({
            'action': 'meet',
            'location': dest,
            'person': friend['name'],
            'start_time': minutes_to_time(meeting_start),
            'end_time': minutes_to_time(meeting_end)
        })
        
        current_time = meeting_end
        current_location = dest
    
    if valid:
        best_itinerary = itinerary
        break

result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))