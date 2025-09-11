import itertools
import json

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_times = {
        'Sunset District': {'North Beach': 29, 'Union Square': 30, 'Alamo Square': 17},
        'North Beach': {'Sunset District': 27, 'Union Square': 7, 'Alamo Square': 16},
        'Union Square': {'Sunset District': 26, 'North Beach': 10, 'Alamo Square': 15},
        'Alamo Square': {'Sunset District': 16, 'North Beach': 15, 'Union Square': 14}
    }
    
    friends = [
        {'name': 'Sarah', 'location': 'North Beach', 'start': 16*60, 'end': 18*60+15, 'min_time': 60},
        {'name': 'Jeffrey', 'location': 'Union Square', 'start': 15*60, 'end': 22*60, 'min_time': 75},
        {'name': 'Brian', 'location': 'Alamo Square', 'start': 16*60, 'end': 17*60+30, 'min_time': 75}
    ]
    
    start_time = 9 * 60
    start_location = 'Sunset District'
    
    best_itinerary = []
    best_count = 0
    
    for r in range(3, 0, -1):
        for perm in itertools.permutations(friends, r):
            current_time = start_time
            current_location = start_location
            itinerary = []
            valid = True
            
            for friend in perm:
                travel_time = travel_times[current_location][friend['location']]
                arrival_time = current_time + travel_time
                meeting_start = max(arrival_time, friend['start'])
                meeting_end = meeting_start + friend['min_time']
                
                if meeting_end <= friend['end']:
                    itinerary.append({
                        "action": "meet",
                        "location": friend['location'],
                        "person": friend['name'],
                        "start_time": format_time(meeting_start),
                        "end_time": format_time(meeting_end)
                    })
                    current_time = meeting_end
                    current_location = friend['location']
                else:
                    valid = False
                    break
            
            if valid and len(itinerary) > best_count:
                best_itinerary = itinerary
                best_count = len(itinerary)
                break
        if best_count > 0:
            break
    
    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()