import itertools
import json

def minutes_to_time(minutes):
    total_minutes = minutes
    hour = 9 + total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

travel_times = {
    'Financial District': {'Chinatown': 5, 'Alamo Square': 17, 'Bayview': 19, "Fisherman's Wharf": 10},
    'Chinatown': {'Financial District': 5, 'Alamo Square': 16, 'Bayview': 22, "Fisherman's Wharf": 12},
    'Alamo Square': {'Financial District': 17, 'Chinatown': 16, 'Bayview': 16, "Fisherman's Wharf": 20},
    'Bayview': {'Financial District': 19, 'Chinatown': 22, 'Alamo Square': 16, "Fisherman's Wharf": 26},
    "Fisherman's Wharf": {'Financial District': 10, 'Chinatown': 12, 'Alamo Square': 20, 'Bayview': 26}
}

friends = [
    {'name': 'Nancy', 'location': 'Chinatown', 'start': 30, 'end': 270, 'min_duration': 90},
    {'name': 'Mary', 'location': 'Alamo Square', 'start': -120, 'end': 720, 'min_duration': 75},
    {'name': 'Jessica', 'location': 'Bayview', 'start': 135, 'end': 285, 'min_duration': 45}
]

best_count = 0
best_schedule = None
best_end_time = float('inf')

for size in range(len(friends), 0, -1):
    for subset in itertools.combinations(friends, size):
        for order in itertools.permutations(subset):
            current_time = 0
            current_location = 'Financial District'
            schedule = []
            feasible = True
            
            for friend in order:
                travel_time = travel_times[current_location][friend['location']]
                current_time += travel_time
                start_meeting = max(current_time, friend['start'])
                if start_meeting > friend['end'] - friend['min_duration']:
                    feasible = False
                    break
                end_meeting = start_meeting + friend['min_duration']
                if end_meeting > friend['end']:
                    feasible = False
                    break
                schedule.append({
                    'action': 'meet',
                    'location': friend['location'],
                    'person': friend['name'],
                    'start_time': minutes_to_time(start_meeting),
                    'end_time': minutes_to_time(end_meeting)
                })
                current_time = end_meeting
                current_location = friend['location']
            
            if feasible:
                if size > best_count:
                    best_count = size
                    best_schedule = schedule
                    best_end_time = current_time
                elif size == best_count and current_time < best_end_time:
                    best_schedule = schedule
                    best_end_time = current_time
    
    if best_count == size and best_schedule is not None:
        break

if best_schedule is None:
    result = {"itinerary": []}
else:
    result = {"itinerary": best_schedule}

print(json.dumps(result))