import itertools
import json

def main():
    travel_times = {
        "Fisherman's Wharf": {
            "The Castro": 26,
            "Golden Gate Park": 25,
            "Embarcadero": 8,
            "Russian Hill": 7,
            "Nob Hill": 11,
            "Alamo Square": 20,
            "North Beach": 6
        },
        "The Castro": {
            "Fisherman's Wharf": 24,
            "Golden Gate Park": 11,
            "Embarcadero": 22,
            "Russian Hill": 18,
            "Nob Hill": 16,
            "Alamo Square": 8,
            "North Beach": 20
        },
        "Golden Gate Park": {
            "Fisherman's Wharf": 24,
            "The Castro": 13,
            "Embarcadero": 25,
            "Russian Hill": 19,
            "Nob Hill": 20,
            "Alamo Square": 10,
            "North Beach": 24
        },
        "Embarcadero": {
            "Fisherman's Wharf": 6,
            "The Castro": 25,
            "Golden Gate Park": 25,
            "Russian Hill": 8,
            "Nob Hill": 10,
            "Alamo Square": 19,
            "North Beach": 5
        },
        "Russian Hill": {
            "Fisherman's Wharf": 7,
            "The Castro": 21,
            "Golden Gate Park": 21,
            "Embarcadero": 8,
            "Nob Hill": 5,
            "Alamo Square": 15,
            "North Beach": 5
        },
        "Nob Hill": {
            "Fisherman's Wharf": 11,
            "The Castro": 17,
            "Golden Gate Park": 17,
            "Embarcadero": 9,
            "Russian Hill": 5,
            "Alamo Square": 11,
            "North Beach": 8
        },
        "Alamo Square": {
            "Fisherman's Wharf": 19,
            "The Castro": 8,
            "Golden Gate Park": 9,
            "Embarcadero": 17,
            "Russian Hill": 13,
            "Nob Hill": 11,
            "North Beach": 15
        },
        "North Beach": {
            "Fisherman's Wharf": 5,
            "The Castro": 22,
            "Golden Gate Park": 22,
            "Embarcadero": 6,
            "Russian Hill": 4,
            "Nob Hill": 7,
            "Alamo Square": 16
        }
    }

    class Friend:
        def __init__(self, name, location, window_start, window_end, min_duration):
            self.name = name
            self.location = location
            self.window_start = window_start
            self.window_end = window_end
            self.min_duration = min_duration

    friends = [
        Friend("Laura", "The Castro", 19*60+45, 21*60+30, 105),
        Friend("Daniel", "Golden Gate Park", 21*60+15, 21*60+45, 15),
        Friend("Karen", "Russian Hill", 14*60+30, 19*60+45, 30),
        Friend("Joseph", "Alamo Square", 11*60+30, 12*60+45, 15),
        Friend("Kimberly", "North Beach", 15*60+45, 19*60+15, 30)
    ]

    start_time = 540
    start_location = "Fisherman's Wharf"
    best_itinerary = None
    best_count = 0

    for perm in itertools.permutations(friends):
        current_time = start_time
        current_location = start_location
        itinerary = []
        count = 0
        for friend in perm:
            travel_time = travel_times[current_location][friend.location]
            arrival_time = current_time + travel_time
            if arrival_time > friend.window_end:
                break
            start_meeting = max(arrival_time, friend.window_start)
            end_meeting = start_meeting + friend.min_duration
            if end_meeting > friend.window_end:
                break
            itinerary.append((friend, start_meeting, end_meeting))
            current_time = end_meeting
            current_location = friend.location
            count += 1
        if count > best_count:
            best_count = count
            best_itinerary = itinerary

    result = {"itinerary": []}
    if best_itinerary:
        for meeting in best_itinerary:
            friend, start, end = meeting
            start_str = f"{start//60}:{start%60:02d}"
            end_str = f"{end//60}:{end%60:02d}"
            result["itinerary"].append({
                "action": "meet",
                "location": friend.location,
                "person": friend.name,
                "start_time": start_str,
                "end_time": end_str
            })

    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()