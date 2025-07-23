import itertools
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    hours = int(parts[0])
    minutes = int(parts[1])
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

travel_times = {
    'Golden Gate Park': {
        'Fisherman\'s Wharf': 24,
        'Bayview': 23,
        'Mission District': 17,
        'Embarcadero': 25,
        'Financial District': 26
    },
    'Fisherman\'s Wharf': {
        'Golden Gate Park': 25,
        'Bayview': 26,
        'Mission District': 22,
        'Embarcadero': 8,
        'Financial District': 11
    },
    'Bayview': {
        'Golden Gate Park': 22,
        'Fisherman\'s Wharf': 25,
        'Mission District': 13,
        'Embarcadero': 19,
        'Financial District': 19
    },
    'Mission District': {
        'Golden Gate Park': 17,
        'Fisherman\'s Wharf': 22,
        'Bayview': 15,
        'Embarcadero': 19,
        'Financial District': 17
    },
    'Embarcadero': {
        'Golden Gate Park': 25,
        'Fisherman\'s Wharf': 6,
        'Bayview': 21,
        'Mission District': 20,
        'Financial District': 5
    },
    'Financial District': {
        'Golden Gate Park': 23,
        'Fisherman\'s Wharf': 10,
        'Bayview': 19,
        'Mission District': 17,
        'Embarcadero': 4
    }
}

friends = [
    {'name': 'Joseph', 'location': "Fisherman\'s Wharf", 'start_available': '8:00', 'end_available': '17:30', 'min_duration': 90},
    {'name': 'Jeffrey', 'location': 'Bayview', 'start_available': '17:30', 'end_available': '21:30', 'min_duration': 60},
    {'name': 'Kevin', 'location': 'Mission District', 'start_available': '11:15', 'end_available': '15:15', 'min_duration': 30},
    {'name': 'Barbara', 'location': 'Financial District', 'start_available': '10:30', 'end_available': '16:30', 'min_duration': 15}
]

found = False
result_itinerary = None

for subset_size in range(4, 0, -1):
    for subset in itertools.combinations(friends, subset_size):
        jeffrey_in_subset = any(f['name'] == 'Jeffrey' for f in subset)
        if jeffrey_in_subset:
            non_jeffrey = [f for f in subset if f['name'] != 'Jeffrey']
            jeffrey = [f for f in subset if f['name'] == 'Jeffrey']
            perms = itertools.permutations(non_jeffrey)
            orderings = [list(p) + jeffrey for p in perms]
        else:
            orderings = itertools.permutations(subset)
        
        for ordering in orderings:
            current_time = 540
            current_location = 'Golden Gate Park'
            itinerary = []
            valid = True
            for friend in ordering:
                try:
                    t = travel_times[current_location][friend['location']]
                except KeyError:
                    valid = False
                    break
                
                arrival_time = current_time + t
                start_avail = time_to_minutes(friend['start_available'])
                end_avail = time_to_minutes(friend['end_available'])
                start_meeting = max(arrival_time, start_avail)
                end_meeting = start_meeting + friend['min_duration']
                
                if end_meeting > end_avail:
                    valid = False
                    break
                
                itinerary.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(start_meeting),
                    'end_time': minutes_to_time(end_meeting)
                })
                
                current_location = friend['location']
                current_time = end_meeting
            
            if valid:
                found = True
                result_itinerary = itinerary
                break
        if found:
            break
    if found:
        break

output = {"itinerary": result_itinerary} if result_itinerary is not None else {"itinerary": []}
print(json.dumps(output))