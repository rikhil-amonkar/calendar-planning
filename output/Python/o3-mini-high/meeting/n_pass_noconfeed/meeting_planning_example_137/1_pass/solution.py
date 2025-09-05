import itertools
import json

def time_to_minutes(t_str):
    hours, minutes = map(int, t_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def compute_itinerary(order, start_time, start_location, travel_times):
    itinerary = []
    current_time = start_time
    current_location = start_location
    for friend in order:
        friend_loc = friend["location"]
        # Travel from current_location to friend's location
        travel_duration = travel_times[(current_location, friend_loc)]
        current_time += travel_duration  # arrival time at friend's location
        
        # Wait if arrived before friend's availability starts
        friend_avail_start = time_to_minutes(friend["avail_start"])
        friend_avail_end = time_to_minutes(friend["avail_end"])
        if current_time < friend_avail_start:
            current_time = friend_avail_start
        
        meet_start = current_time
        meet_end = meet_start + friend["min_duration"]
        
        # Check if we can meet the friend for the required duration within their available window
        if meet_end > friend_avail_end:
            return None, None
        
        itinerary.append({
            "action": "meet",
            "location": friend_loc,
            "person": friend["name"],
            "start_time": minutes_to_time(meet_start),
            "end_time": minutes_to_time(meet_end)
        })
        current_time = meet_end
        current_location = friend_loc
    return current_time, itinerary

def main():
    # Starting point: Arrive at Financial District at 9:00
    start_location = "Financial District"
    start_time = time_to_minutes("9:00")
    
    # Travel durations between locations (in minutes)
    travel_times = {
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Golden Gate Park"): 23,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Chinatown"): 23
    }
    
    # Friend meeting constraints
    friends = [
        {
            "name": "Kenneth",
            "location": "Chinatown",
            "avail_start": "12:00",
            "avail_end": "15:00",
            "min_duration": 90  # minutes
        },
        {
            "name": "Barbara",
            "location": "Golden Gate Park",
            "avail_start": "8:15",
            "avail_end": "19:00",
            "min_duration": 45  # minutes
        }
    ]
    
    best_itinerary = None
    best_finish_time = None
    
    # Try every order (permutation) for meeting the friends
    for order in itertools.permutations(friends):
        finish_time, itinerary = compute_itinerary(order, start_time, start_location, travel_times)
        if finish_time is not None:
            if best_finish_time is None or finish_time < best_finish_time:
                best_finish_time = finish_time
                best_itinerary = itinerary

    # Prepare output JSON structure
    result = {"itinerary": best_itinerary if best_itinerary is not None else []}
    print(json.dumps(result))

if __name__ == "__main__":
    main()