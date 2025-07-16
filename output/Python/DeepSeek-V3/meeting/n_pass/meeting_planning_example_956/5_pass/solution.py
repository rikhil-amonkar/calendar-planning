import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times between locations in minutes
travel_times = {
    "The Castro": {
        "The Castro": 0,
        "Mission District": 10,
        "SOMA": 15,
        "Nob Hill": 20,
        "North Beach": 25,
        "Haight": 15
    },
    "Mission District": {
        "The Castro": 10,
        "Mission District": 0,
        "SOMA": 10,
        "Nob Hill": 15,
        "North Beach": 20,
        "Haight": 20
    },
    "SOMA": {
        "The Castro": 15,
        "Mission District": 10,
        "SOMA": 0,
        "Nob Hill": 10,
        "North Beach": 15,
        "Haight": 25
    },
    "Nob Hill": {
        "The Castro": 20,
        "Mission District": 15,
        "SOMA": 10,
        "Nob Hill": 0,
        "North Beach": 5,
        "Haight": 15
    },
    "North Beach": {
        "The Castro": 25,
        "Mission District": 20,
        "SOMA": 15,
        "Nob Hill": 5,
        "North Beach": 0,
        "Haight": 20
    },
    "Haight": {
        "The Castro": 15,
        "Mission District": 20,
        "SOMA": 25,
        "Nob Hill": 15,
        "North Beach": 20,
        "Haight": 0
    }
}

friends = [
    {"name": "Alice", "location": "Mission District", "start": "9:30", "end": "10:30", "duration": 30},
    {"name": "Bob", "location": "North Beach", "start": "10:00", "end": "12:00", "duration": 45},
    {"name": "Charlie", "location": "SOMA", "start": "10:30", "end": "12:30", "duration": 30},
    {"name": "Dana", "location": "Haight", "start": "11:00", "end": "12:30", "duration": 30},
    {"name": "Eve", "location": "Nob Hill", "start": "9:00", "end": "11:00", "duration": 60}
]

def find_best_itinerary():
    max_friends = 0
    best_itinerary = []
    
    # Try all possible orders of friends (limit to 5 to prevent excessive computation)
    for friend_order in permutations(friends, min(5, len(friends))):
        current_location = "The Castro"
        current_time = time_to_minutes("9:00")
        itinerary = []
        scheduled_friends = set()
        
        for friend in friend_order:
            if friend["name"] in scheduled_friends:
                continue
                
            # Calculate travel time
            travel = travel_times[current_location][friend["location"]]
            arrival = current_time + travel
            start = max(arrival, time_to_minutes(friend["start"]))
            end = start + friend["duration"]
            
            # Check if meeting is possible
            if end <= time_to_minutes(friend["end"]):
                itinerary.append({
                    "action": "meet",
                    "location": friend["location"],
                    "person": friend["name"],
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
                scheduled_friends.add(friend["name"])
                current_time = end
                current_location = friend["location"]
        
        # Update best itinerary if this one schedules more friends
        if len(itinerary) > max_friends:
            max_friends = len(itinerary)
            best_itinerary = itinerary.copy()
            
            # Early exit if we've scheduled all friends
            if max_friends == len(friends):
                break
    
    return best_itinerary

best_itinerary = find_best_itinerary()

if best_itinerary:
    result = {"itinerary": best_itinerary}
else:
    result = {"itinerary": []}

print(json.dumps(result, indent=2))