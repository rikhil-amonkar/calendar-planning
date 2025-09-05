import json
import itertools

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def schedule_permutation(order, start_location, start_time, travel_times, friend_data):
    itinerary = []
    current_location = start_location
    current_time = start_time
    for friend in order:
        info = friend_data[friend]
        friend_loc = info["location"]
        avail_start = info["available_start"]
        avail_end = info["available_end"]
        duration = info["duration"]
        travel_time = travel_times[(current_location, friend_loc)]
        arrival_time = current_time + travel_time
        # Wait until the friend's availability window opens, if needed.
        meeting_start = max(arrival_time, avail_start)
        meeting_end = meeting_start + duration
        if meeting_end > avail_end:
            return None  # This schedule is not feasible
        itinerary.append({
            "action": "meet",
            "location": friend_loc,
            "person": friend,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        current_location = friend_loc
        current_time = meeting_end
    return itinerary

def main():
    # Input parameters
    start_location = "Bayview"
    start_time = 9 * 60  # 9:00 AM in minutes
    
    # Friend meeting data: times in minutes from midnight.
    friend_data = {
        "Jessica": {
            "location": "Embarcadero",
            "available_start": 16 * 60 + 45,  # 16:45
            "available_end": 19 * 60,         # 19:00
            "duration": 30
        },
        "Sandra": {
            "location": "Richmond District",
            "available_start": 18 * 60 + 30,  # 18:30
            "available_end": 21 * 60 + 45,      # 21:45
            "duration": 120
        },
        "Jason": {
            "location": "Fisherman's Wharf",
            "available_start": 16 * 60,       # 16:00
            "available_end": 16 * 60 + 45,      # 16:45
            "duration": 30
        }
    }
    
    # Travel distances (in minutes) between locations.
    travel_times = {
        ("Bayview", "Embarcadero"): 19,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Embarcadero", "Bayview"): 21,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Richmond District", "Bayview"): 26,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Richmond District"): 18
    }
    
    # Evaluate all possible meeting orders to maximize the number of meetings.
    friends = list(friend_data.keys())
    best_itinerary = None
    best_count = 0
    for order in itertools.permutations(friends):
        itinerary = schedule_permutation(order, start_location, start_time, travel_times, friend_data)
        if itinerary is not None:
            if len(itinerary) > best_count:
                best_count = len(itinerary)
                best_itinerary = itinerary
                
    result = {"itinerary": best_itinerary if best_itinerary is not None else []}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()