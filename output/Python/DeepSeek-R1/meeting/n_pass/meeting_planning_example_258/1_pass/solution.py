import json
from itertools import permutations

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes_remain = minutes % 60
    return f"{hours}:{minutes_remain:02d}"

def try_schedule(permutation, start_location, start_time, travel_times):
    current_location = start_location
    current_time = start_time
    schedule = []
    for friend in permutation:
        travel_time = travel_times[current_location][friend['location']]
        arrival = current_time + travel_time
        meeting_start = max(arrival, friend['start_available'])
        if meeting_start > friend['end_available'] - friend['min_duration']:
            return None
        meeting_end = meeting_start + friend['min_duration']
        schedule.append({
            'person': friend['name'],
            'location': friend['location'],
            'start_time': meeting_start,
            'end_time': meeting_end
        })
        current_location = friend['location']
        current_time = meeting_end
    return schedule

def main():
    travel_times = {
        "Embarcadero": {"Presidio": 20, "Richmond District": 21, "Fisherman's Wharf": 6},
        "Presidio": {"Embarcadero": 20, "Richmond District": 7, "Fisherman's Wharf": 17},
        "Richmond District": {"Embarcadero": 19, "Presidio": 7, "Fisherman's Wharf": 18},
        "Fisherman's Wharf": {"Embarcadero": 8, "Presidio": 17, "Richmond District": 18}
    }
    
    friends = [
        {'name': 'Betty', 'location': 'Presidio', 'start_available': 615, 'end_available': 1290, 'min_duration': 45},
        {'name': 'David', 'location': 'Richmond District', 'start_available': 780, 'end_available': 1215, 'min_duration': 90},
        {'name': 'Barbara', 'location': "Fisherman's Wharf", 'start_available': 555, 'end_available': 1215, 'min_duration': 120}
    ]
    
    start_location = "Embarcadero"
    start_time = 540
    
    best_schedule = None
    
    for perm in permutations(friends):
        candidate = try_schedule(perm, start_location, start_time, travel_times)
        if candidate is not None:
            best_schedule = candidate
            break
    
    if best_schedule is None:
        for perm in permutations(friends, 2):
            candidate = try_schedule(perm, start_location, start_time, travel_times)
            if candidate is not None:
                best_schedule = candidate
                break
    
    if best_schedule is None:
        for friend in friends:
            candidate = try_schedule([friend], start_location, start_time, travel_times)
            if candidate is not None:
                best_schedule = candidate
                break
    
    itinerary = []
    for event in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": event['location'],
            "person": event['person'],
            "start_time": minutes_to_time(event['start_time']),
            "end_time": minutes_to_time(event['end_time'])
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == '__main__':
    main()