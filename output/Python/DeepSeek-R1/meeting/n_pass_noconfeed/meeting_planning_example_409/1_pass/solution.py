import itertools
import json

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def main():
    travel_times = {
        "Fisherman's Wharf": {
            "Bayview": 26,
            "Golden Gate Park": 25,
            "Nob Hill": 11,
            "Marina District": 9,
            "Embarcadero": 8
        },
        "Bayview": {
            "Fisherman's Wharf": 25,
            "Golden Gate Park": 22,
            "Nob Hill": 20,
            "Marina District": 25,
            "Embarcadero": 19
        },
        "Golden Gate Park": {
            "Fisherman's Wharf": 24,
            "Bayview": 23,
            "Nob Hill": 20,
            "Marina District": 16,
            "Embarcadero": 25
        },
        "Nob Hill": {
            "Fisherman's Wharf": 11,
            "Bayview": 19,
            "Golden Gate Park": 17,
            "Marina District": 11,
            "Embarcadero": 9
        },
        "Marina District": {
            "Fisherman's Wharf": 10,
            "Bayview": 27,
            "Golden Gate Park": 18,
            "Nob Hill": 12,
            "Embarcadero": 14
        },
        "Embarcadero": {
            "Fisherman's Wharf": 6,
            "Bayview": 21,
            "Golden Gate Park": 25,
            "Nob Hill": 10,
            "Marina District": 12
        }
    }
    
    friends = [
        {'name': 'Thomas', 'location': 'Bayview', 'start': 15*60+30, 'end': 18*60+30, 'min_duration': 120},
        {'name': 'Stephanie', 'location': 'Golden Gate Park', 'start': 18*60+30, 'end': 21*60+45, 'min_duration': 30},
        {'name': 'Laura', 'location': 'Nob Hill', 'start': 8*60+45, 'end': 16*60+15, 'min_duration': 30},
        {'name': 'Betty', 'location': 'Marina District', 'start': 18*60+45, 'end': 21*60+45, 'min_duration': 45},
        {'name': 'Patricia', 'location': 'Embarcadero', 'start': 17*60+30, 'end': 22*60, 'min_duration': 45}
    ]
    
    start_time = 9 * 60
    start_location = "Fisherman's Wharf"
    
    max_count = 0
    best_schedule = None
    
    for perm in itertools.permutations(friends):
        current_location = start_location
        current_time = start_time
        schedule = []
        for friend in perm:
            tt = travel_times[current_location][friend['location']]
            current_time += tt
            if current_time > friend['end']:
                current_location = friend['location']
                continue
            if current_time < friend['start']:
                current_time = friend['start']
            if current_time + friend['min_duration'] > friend['end']:
                current_location = friend['location']
                continue
            end_time = current_time + friend['min_duration']
            schedule.append({
                'action': 'meet',
                'location': friend['location'],
                'person': friend['name'],
                'start_time': format_time(current_time),
                'end_time': format_time(end_time)
            })
            current_time = end_time
            current_location = friend['location']
        count = len(schedule)
        if count > max_count:
            max_count = count
            best_schedule = schedule
            if max_count == 5:
                break
    
    if best_schedule is None:
        best_schedule = []
    
    result = {
        "itinerary": best_schedule
    }
    print(json.dumps(result))

if __name__ == '__main__':
    main()