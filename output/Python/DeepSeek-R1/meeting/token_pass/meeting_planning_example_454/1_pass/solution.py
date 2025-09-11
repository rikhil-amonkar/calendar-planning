import itertools
import json

def time_to_minutes(time_str):
    parts = time_str.split(':')
    return int(parts[0]) * 60 + int(parts[1])

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    travel_matrix = {
        "Presidio": {
            "Golden Gate Park": 12,
            "Bayview": 31,
            "Chinatown": 21,
            "North Beach": 18,
            "Mission District": 26
        },
        "Golden Gate Park": {
            "Presidio": 11,
            "Bayview": 23,
            "Chinatown": 23,
            "North Beach": 24,
            "Mission District": 17
        },
        "Bayview": {
            "Presidio": 31,
            "Golden Gate Park": 22,
            "Chinatown": 18,
            "North Beach": 21,
            "Mission District": 13
        },
        "Chinatown": {
            "Presidio": 19,
            "Golden Gate Park": 23,
            "Bayview": 22,
            "North Beach": 3,
            "Mission District": 18
        },
        "North Beach": {
            "Presidio": 17,
            "Golden Gate Park": 22,
            "Bayview": 22,
            "Chinatown": 6,
            "Mission District": 18
        },
        "Mission District": {
            "Presidio": 25,
            "Golden Gate Park": 17,
            "Bayview": 15,
            "Chinatown": 16,
            "North Beach": 17
        }
    }
    
    friends = [
        {"name": "Jessica", "location": "Golden Gate Park", "available_start": time_to_minutes("13:45"), "available_end": time_to_minutes("15:00"), "min_duration": 30},
        {"name": "Ashley", "location": "Bayview", "available_start": time_to_minutes("17:15"), "available_end": time_to_minutes("20:00"), "min_duration": 105},
        {"name": "Ronald", "location": "Chinatown", "available_start": time_to_minutes("7:15"), "available_end": time_to_minutes("14:45"), "min_duration": 90},
        {"name": "William", "location": "North Beach", "available_start": time_to_minutes("13:15"), "available_end": time_to_minutes("20:15"), "min_duration": 15},
        {"name": "Daniel", "location": "Mission District", "available_start": time_to_minutes("7:00"), "available_end": time_to_minutes("11:15"), "min_duration": 105}
    ]
    
    start_time = time_to_minutes("9:00")
    start_location = "Presidio"
    best_count = 0
    best_itinerary = []
    
    for perm in itertools.permutations(friends):
        current_time = start_time
        current_location = start_location
        itinerary = []
        count = 0
        for friend in perm:
            travel_time = travel_matrix[current_location][friend['location']]
            current_time += travel_time
            if current_time < friend['available_start']:
                current_time = friend['available_start']
            end_time = current_time + friend['min_duration']
            if end_time <= friend['available_end']:
                itinerary.append({
                    "action": "meet",
                    "location": friend['location'],
                    "person": friend['name'],
                    "start_time": minutes_to_time(current_time),
                    "end_time": minutes_to_time(end_time)
                })
                current_time = end_time
                current_location = friend['location']
                count += 1
            else:
                break
        if count > best_count:
            best_count = count
            best_itinerary = itinerary
    
    result = {"itinerary": best_itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()