import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times dictionary remains the same
travel_times = {
    # ... (same travel_times dictionary as before)
}

friends = [
    # ... (same friends list as before)
]

def find_best_itinerary():
    max_friends = 0
    best_itinerary = []
    
    # Try different friend orders with a smarter approach
    for friend_order in permutations(friends, min(5, len(friends))):  # Still limit permutations but smarter
        current_location = "The Castro"
        current_time = time_to_minutes("9:00")
        itinerary = []
        remaining_friends = friends.copy()
        
        for friend in friend_order:
            if friend not in remaining_friends:
                continue
                
            travel = travel_times[current_location][friend["location"]]
            arrival = current_time + travel
            start = max(arrival, time_to_minutes(friend["start"]))
            end = start + friend["duration"]
            
            if end > time_to_minutes(friend["end"]):
                continue  # Skip this friend in this order
                
            itinerary.append({
                "action": "meet",
                "location": friend["location"],
                "person": friend["name"],
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
            
            current_time = end
            current_location = friend["location"]
            remaining_friends.remove(friend)
            
            # Try to add remaining friends in order of earliest end time
            remaining_friends_sorted = sorted(
                remaining_friends,
                key=lambda x: (
                    time_to_minutes(x["end"]),
                    time_to_minutes(x["start"])
                )
            
            for remaining_friend in remaining_friends_sorted:
                travel = travel_times[current_location][remaining_friend["location"]]
                arrival = current_time + travel
                start = max(arrival, time_to_minutes(remaining_friend["start"]))
                end = start + remaining_friend["duration"]
                
                if end > time_to_minutes(remaining_friend["end"]):
                    continue
                    
                itinerary.append({
                    "action": "meet",
                    "location": remaining_friend["location"],
                    "person": remaining_friend["name"],
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
                
                current_time = end
                current_location = remaining_friend["location"]
                remaining_friends.remove(remaining_friend)
        
        if len(itinerary) > max_friends:
            max_friends = len(itinerary)
            best_itinerary = itinerary.copy()
            
            if max_friends == len(friends):  # Found optimal solution
                break
    
    return best_itinerary

best_itinerary = find_best_itinerary()

if best_itinerary:
    result = {"itinerary": best_itinerary}
else:
    result = {"itinerary": []}

print(json.dumps(result, indent=2))