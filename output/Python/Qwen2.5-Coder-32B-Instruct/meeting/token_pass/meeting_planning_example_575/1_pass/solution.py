import json
from datetime import datetime, timedelta

# Define travel times as a dictionary of dictionaries
travel_times = {
    "The Castro": {"Presidio": 20, "Sunset District": 17, "Haight-Ashbury": 6, "Mission District": 7, "Golden Gate Park": 11, "Russian Hill": 18},
    "Presidio": {"The Castro": 21, "Sunset District": 15, "Haight-Ashbury": 15, "Mission District": 26, "Golden Gate Park": 12, "Russian Hill": 14},
    "Sunset District": {"The Castro": 17, "Presidio": 16, "Haight-Ashbury": 15, "Mission District": 24, "Golden Gate Park": 11, "Russian Hill": 24},
    "Haight-Ashbury": {"The Castro": 6, "Presidio": 15, "Sunset District": 15, "Mission District": 11, "Golden Gate Park": 7, "Russian Hill": 17},
    "Mission District": {"The Castro": 7, "Presidio": 25, "Sunset District": 24, "Haight-Ashbury": 12, "Golden Gate Park": 17, "Russian Hill": 15},
    "Golden Gate Park": {"The Castro": 13, "Presidio": 11, "Sunset District": 10, "Haight-Ashbury": 7, "Mission District": 17, "Russian Hill": 19},
    "Russian Hill": {"The Castro": 21, "Presidio": 14, "Sunset District": 23, "Haight-Ashbury": 17, "Mission District": 16, "Golden Gate Park": 21}
}

# Define friend availabilities and meeting durations
friends = {
    "Rebecca": {"location": "Presidio", "available": (datetime.strptime("18:15", "%H:%M"), datetime.strptime("20:45", "%H:%M")), "duration": 60},
    "Linda": {"location": "Sunset District", "available": (datetime.strptime("15:30", "%H:%M"), datetime.strptime("19:45", "%H:%M")), "duration": 30},
    "Elizabeth": {"location": "Haight-Ashbury", "available": (datetime.strptime("17:15", "%H:%M"), datetime.strptime("19:30", "%H:%M")), "duration": 105},
    "William": {"location": "Mission District", "available": (datetime.strptime("13:15", "%H:%M"), datetime.strptime("19:30", "%H:%M")), "duration": 30},
    "Robert": {"location": "Golden Gate Park", "available": (datetime.strptime("14:15", "%H:%M"), datetime.strptime("21:30", "%H:%M")), "duration": 45},
    "Mark": {"location": "Russian Hill", "available": (datetime.strptime("10:00", "%H:%M"), datetime.strptime("21:15", "%H:%M")), "duration": 75}
}

def time_to_str(time):
    return time.strftime("%H:%M")

def str_to_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def can_meet(current_time, friend_info):
    start, end = friend_info["available"]
    duration = friend_info["duration"]
    return start <= current_time + timedelta(minutes=duration) <= end

def backtrack(current_location, current_time, visited_friends, itinerary):
    global best_itinerary
    if len(visited_friends) == len(friends):
        if len(itinerary) > len(best_itinerary):
            best_itinerary = itinerary[:]
        return
    
    for friend, info in friends.items():
        if friend not in visited_friends and info["location"] != current_location:
            travel_duration = travel_times[current_location][info["location"]]
            new_time = current_time + timedelta(minutes=travel_duration)
            if can_meet(new_time, info):
                new_end_time = new_time + timedelta(minutes=info["duration"])
                itinerary.append({
                    "action": "meet",
                    "location": info["location"],
                    "person": friend,
                    "start_time": time_to_str(new_time),
                    "end_time": time_to_str(new_end_time)
                })
                visited_friends.add(friend)
                backtrack(info["location"], new_end_time, visited_friends, itinerary)
                visited_friends.remove(friend)
                itinerary.pop()

best_itinerary = []
backtrack("The Castro", str_to_time("9:00"), set(), [])

# Output the best itinerary in JSON format
output = {"itinerary": best_itinerary}
print(json.dumps(output, indent=2))