import json
from datetime import datetime, timedelta

def time_to_str(t):
    return f"{t.hour}:{t.minute:02d}"

def str_to_time(s):
    return datetime.strptime(s, "%H:%M")

def compute_schedule():
    # Travel times in minutes
    travel = {
        ("Bayview", "Union Square"): 17,
        ("Bayview", "Presidio"): 31,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Presidio"): 24,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Union Square"): 22,
    }
    
    # Constraints
    start_location = "Bayview"
    start_time = str_to_time("9:00")
    
    friends = [
        {
            "name": "Richard",
            "location": "Union Square",
            "available_start": str_to_time("8:45"),
            "available_end": str_to_time("13:00"),
            "min_duration": 120,
        },
        {
            "name": "Charles",
            "location": "Presidio",
            "available_start": str_to_time("9:45"),
            "available_end": str_to_time("13:00"),
            "min_duration": 120,
        }
    ]
    
    # Try both orders
    best_itinerary = []
    max_meetings = 0
    
    from itertools import permutations
    for perm in permutations(friends):
        current_time = start_time
        current_loc = start_location
        itinerary = []
        meetings_count = 0
        
        for friend in perm:
            # Travel to friend's location
            travel_key = (current_loc, friend["location"])
            travel_duration = travel[travel_key]
            arrive_time = current_time + timedelta(minutes=travel_duration)
            
            # Start meeting at earliest possible time after arrival
            meet_start = max(arrive_time, friend["available_start"])
            # End meeting at minimum duration
            meet_end = meet_start + timedelta(minutes=friend["min_duration"])
            
            # Check if meeting fits in availability
            if meet_end <= friend["available_end"]:
                meetings_count += 1
                itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": time_to_str(meet_start),
                    "end_time": time_to_str(meet_end),
                })
                current_time = meet_end
                current_loc = friend["location"]
            else:
                # This meeting not possible in this order
                break
        
        if meetings_count > max_meetings:
            max_meetings = meetings_count
            best_itinerary = itinerary
    
    # If no order allows both, just pick one friend (first in list)
    if max_meetings == 0:
        friend = friends[0]
        travel_key = (start_location, friend["location"])
        travel_duration = travel[travel_key]
        arrive_time = start_time + timedelta(minutes=travel_duration)
        meet_start = max(arrive_time, friend["available_start"])
        meet_end = meet_start + timedelta(minutes=friend["min_duration"])
        if meet_end > friend["available_end"]:
            # Adjust to fit within available time
            meet_end = friend["available_end"]
            meet_start = meet_end - timedelta(minutes=friend["min_duration"])
            if meet_start < friend["available_start"]:
                meet_start = friend["available_start"]
        best_itinerary = [{
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": time_to_str(meet_start),
            "end_time": time_to_str(meet_end),
        }]
    
    return {"itinerary": best_itinerary}

if __name__ == "__main__":
    result = compute_schedule()
    print(json.dumps(result, indent=2))