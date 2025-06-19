import json
from itertools import combinations, permutations

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    mary = {"name": "Mary", "location": "Pacific Heights", "start": 10*60, "end": 19*60, "min_duration": 45}
    lisa = {"name": "Lisa", "location": "Mission District", "start": 20*60+30, "end": 22*60, "min_duration": 75}
    betty = {"name": "Betty", "location": "Haight-Ashbury", "start": 7*60+15, "end": 17*60+15, "min_duration": 90}
    charles = {"name": "Charles", "location": "Financial District", "start": 11*60+15, "end": 15*60, "min_duration": 120}
    friends = [mary, lisa, betty, charles]
    
    travel_times = {
        "Bayview": {
            "Pacific Heights": 23,
            "Mission District": 13,
            "Haight-Ashbury": 19,
            "Financial District": 19
        },
        "Pacific Heights": {
            "Bayview": 22,
            "Mission District": 15,
            "Haight-Ashbury": 11,
            "Financial District": 13
        },
        "Mission District": {
            "Bayview": 15,
            "Pacific Heights": 16,
            "Haight-Ashbury": 12,
            "Financial District": 17
        },
        "Haight-Ashbury": {
            "Bayview": 18,
            "Pacific Heights": 12,
            "Mission District": 11,
            "Financial District": 21
        },
        "Financial District": {
            "Bayview": 19,
            "Pacific Heights": 13,
            "Mission District": 17,
            "Haight-Ashbury": 19
        }
    }
    
    start_time_val = 9 * 60
    start_location = "Bayview"
    
    n = len(friends)
    indices = list(range(n))
    all_subsets = []
    for r in range(0, n+1):
        for subset in combinations(indices, r):
            all_subsets.append(subset)
    
    best_count = -1
    best_itinerary = None
    
    for subset in all_subsets:
        for order in permutations(subset):
            current_location = start_location
            current_time = start_time_val
            itinerary = []
            valid = True
            for idx in order:
                friend = friends[idx]
                try:
                    t = travel_times[current_location][friend['location']]
                except KeyError:
                    valid = False
                    break
                    
                arrival_time = current_time + t
                start_meeting = max(arrival_time, friend['start'])
                end_meeting = start_meeting + friend['min_duration']
                
                if end_meeting > friend['end']:
                    valid = False
                    break
                    
                itinerary.append({
                    "action": "meet",
                    "location": friend['location'],
                    "person": friend['name'],
                    "start_time": minutes_to_time(start_meeting),
                    "end_time": minutes_to_time(end_meeting)
                })
                
                current_time = end_meeting
                current_location = friend['location']
                
            if valid:
                if len(subset) > best_count:
                    best_count = len(subset)
                    best_itinerary = itinerary
                    
    if best_itinerary is None:
        best_itinerary = []
        
    result = {"itinerary": best_itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()