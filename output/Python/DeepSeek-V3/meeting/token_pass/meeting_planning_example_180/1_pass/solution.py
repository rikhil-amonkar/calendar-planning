import json
from datetime import datetime, timedelta

def time_to_str(t):
    return f"{t.hour}:{t.minute:02d}"

def str_to_time(s):
    return datetime.strptime(s, "%H:%M")

def compute_schedule():
    # Travel times in minutes
    travel = {
        ("North Beach", "Mission District"): 18,
        ("North Beach", "The Castro"): 22,
        ("Mission District", "North Beach"): 17,
        ("Mission District", "The Castro"): 7,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Mission District"): 7,
    }
    
    # Start
    current_time = str_to_time("9:00")
    start_location = "North Beach"
    
    # Friend constraints
    friends = [
        {
            "name": "James",
            "location": "Mission District",
            "window_start": str_to_time("12:45"),
            "window_end": str_to_time("14:00"),
            "duration_min": 75,
        },
        {
            "name": "Robert",
            "location": "The Castro",
            "window_start": str_to_time("12:45"),
            "window_end": str_to_time("15:15"),
            "duration_min": 30,
        }
    ]
    
    # Try both permutations
    from itertools import permutations
    best_itinerary = []
    best_meetings = 0
    
    for perm in permutations([0, 1]):
        itinerary = []
        current_loc = start_location
        current_time = str_to_time("9:00")
        possible = True
        meetings = 0
        
        for idx in perm:
            friend = friends[idx]
            # Travel to friend's location
            travel_key = (current_loc, friend["location"])
            travel_min = travel.get(travel_key)
            if travel_min is None:
                possible = False
                break
            
            arrival_time = current_time + timedelta(minutes=travel_min)
            
            # If we arrive before window, wait until window starts
            if arrival_time < friend["window_start"]:
                arrival_time = friend["window_start"]
            
            # Check if we can meet for required duration
            meeting_end = arrival_time + timedelta(minutes=friend["duration_min"])
            if meeting_end > friend["window_end"]:
                possible = False
                break
            
            # Add meeting to itinerary
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": time_to_str(arrival_time),
                "end_time": time_to_str(meeting_end),
            })
            
            meetings += 1
            current_time = meeting_end
            current_loc = friend["location"]
        
        if possible and meetings > best_meetings:
            best_meetings = meetings
            best_itinerary = itinerary
    
    # If both can't be met, try each alone
    if best_meetings < 2:
        for friend in friends:
            # Travel from start to friend
            travel_key = (start_location, friend["location"])
            travel_min = travel.get(travel_key)
            arrival_time = str_to_time("9:00") + timedelta(minutes=travel_min)
            if arrival_time < friend["window_start"]:
                arrival_time = friend["window_start"]
            meeting_end = arrival_time + timedelta(minutes=friend["duration_min"])
            if meeting_end <= friend["window_end"]:
                itinerary = [{
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": time_to_str(arrival_time),
                    "end_time": time_to_str(meeting_end),
                }]
                if 1 > best_meetings:
                    best_meetings = 1
                    best_itinerary = itinerary
    
    return {"itinerary": best_itinerary}

if __name__ == "__main__":
    result = compute_schedule()
    print(json.dumps(result, indent=2))