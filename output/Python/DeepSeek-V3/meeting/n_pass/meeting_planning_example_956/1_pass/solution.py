import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Travel times dictionary: {from_location: {to_location: minutes}}
travel_times = {
    "The Castro": {
        "Alamo Square": 8,
        "Richmond District": 16,
        "Financial District": 21,
        "Union Square": 19,
        "Fisherman's Wharf": 24,
        "Marina District": 21,
        "Haight-Ashbury": 6,
        "Mission District": 7,
        "Pacific Heights": 16,
        "Golden Gate Park": 11
    },
    "Alamo Square": {
        "The Castro": 8,
        "Richmond District": 11,
        "Financial District": 17,
        "Union Square": 14,
        "Fisherman's Wharf": 19,
        "Marina District": 15,
        "Haight-Ashbury": 5,
        "Mission District": 10,
        "Pacific Heights": 10,
        "Golden Gate Park": 9
    },
    "Richmond District": {
        "The Castro": 16,
        "Alamo Square": 13,
        "Financial District": 22,
        "Union Square": 21,
        "Fisherman's Wharf": 18,
        "Marina District": 9,
        "Haight-Ashbury": 10,
        "Mission District": 20,
        "Pacific Heights": 10,
        "Golden Gate Park": 9
    },
    "Financial District": {
        "The Castro": 20,
        "Alamo Square": 17,
        "Richmond District": 21,
        "Union Square": 9,
        "Fisherman's Wharf": 10,
        "Marina District": 15,
        "Haight-Ashbury": 19,
        "Mission District": 17,
        "Pacific Heights": 13,
        "Golden Gate Park": 23
    },
    "Union Square": {
        "The Castro": 17,
        "Alamo Square": 15,
        "Richmond District": 20,
        "Financial District": 9,
        "Fisherman's Wharf": 15,
        "Marina District": 18,
        "Haight-Ashbury": 18,
        "Mission District": 14,
        "Pacific Heights": 15,
        "Golden Gate Park": 22
    },
    "Fisherman's Wharf": {
        "The Castro": 27,
        "Alamo Square": 21,
        "Richmond District": 18,
        "Financial District": 11,
        "Union Square": 13,
        "Marina District": 9,
        "Haight-Ashbury": 22,
        "Mission District": 22,
        "Pacific Heights": 12,
        "Golden Gate Park": 25
    },
    "Marina District": {
        "The Castro": 22,
        "Alamo Square": 15,
        "Richmond District": 11,
        "Financial District": 17,
        "Union Square": 16,
        "Fisherman's Wharf": 10,
        "Haight-Ashbury": 16,
        "Mission District": 20,
        "Pacific Heights": 7,
        "Golden Gate Park": 18
    },
    "Haight-Ashbury": {
        "The Castro": 6,
        "Alamo Square": 5,
        "Richmond District": 10,
        "Financial District": 21,
        "Union Square": 19,
        "Fisherman's Wharf": 23,
        "Marina District": 17,
        "Mission District": 11,
        "Pacific Heights": 12,
        "Golden Gate Park": 7
    },
    "Mission District": {
        "The Castro": 7,
        "Alamo Square": 11,
        "Richmond District": 20,
        "Financial District": 15,
        "Union Square": 15,
        "Fisherman's Wharf": 22,
        "Marina District": 19,
        "Haight-Ashbury": 12,
        "Pacific Heights": 16,
        "Golden Gate Park": 17
    },
    "Pacific Heights": {
        "The Castro": 16,
        "Alamo Square": 10,
        "Richmond District": 12,
        "Financial District": 13,
        "Union Square": 12,
        "Fisherman's Wharf": 13,
        "Marina District": 6,
        "Haight-Ashbury": 11,
        "Mission District": 15,
        "Golden Gate Park": 15
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Alamo Square": 9,
        "Richmond District": 7,
        "Financial District": 26,
        "Union Square": 22,
        "Fisherman's Wharf": 24,
        "Marina District": 16,
        "Haight-Ashbury": 7,
        "Mission District": 17,
        "Pacific Heights": 16
    }
}

# Friend constraints
friends = [
    {"name": "William", "location": "Alamo Square", "start": "15:15", "end": "17:15", "duration": 60},
    {"name": "Joshua", "location": "Richmond District", "start": "7:00", "end": "20:00", "duration": 15},
    {"name": "Joseph", "location": "Financial District", "start": "11:15", "end": "13:30", "duration": 15},
    {"name": "David", "location": "Union Square", "start": "16:45", "end": "19:15", "duration": 45},
    {"name": "Brian", "location": "Fisherman's Wharf", "start": "13:45", "end": "20:45", "duration": 105},
    {"name": "Karen", "location": "Marina District", "start": "11:30", "end": "18:30", "duration": 15},
    {"name": "Anthony", "location": "Haight-Ashbury", "start": "7:15", "end": "10:30", "duration": 30},
    {"name": "Matthew", "location": "Mission District", "start": "17:15", "end": "19:15", "duration": 120},
    {"name": "Helen", "location": "Pacific Heights", "start": "8:00", "end": "12:00", "duration": 75},
    {"name": "Jeffrey", "location": "Golden Gate Park", "start": "19:00", "end": "21:30", "duration": 60}
]

def calculate_schedule():
    current_time = time_to_minutes("9:00")
    current_location = "The Castro"
    itinerary = []
    remaining_friends = friends.copy()
    
    # First, meet Anthony (earliest availability)
    anthony = next(f for f in remaining_friends if f["name"] == "Anthony")
    travel = travel_times[current_location][anthony["location"]]
    arrival = current_time + travel
    start = max(arrival, time_to_minutes(anthony["start"]))
    end = start + anthony["duration"]
    if end > time_to_minutes(anthony["end"]):
        return None  # Can't meet this friend
    itinerary.append({
        "action": "meet",
        "location": anthony["location"],
        "person": anthony["name"],
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    })
    current_time = end
    current_location = anthony["location"]
    remaining_friends.remove(anthony)
    
    # Next, meet Helen (must be done before 12:00)
    helen = next(f for f in remaining_friends if f["name"] == "Helen")
    travel = travel_times[current_location][helen["location"]]
    arrival = current_time + travel
    start = max(arrival, time_to_minutes(helen["start"]))
    end = start + helen["duration"]
    if end > time_to_minutes(helen["end"]):
        return None
    itinerary.append({
        "action": "meet",
        "location": helen["location"],
        "person": helen["name"],
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    })
    current_time = end
    current_location = helen["location"]
    remaining_friends.remove(helen)
    
    # Next, meet Joseph (11:15-13:30)
    joseph = next(f for f in remaining_friends if f["name"] == "Joseph")
    travel = travel_times[current_location][joseph["location"]]
    arrival = current_time + travel
    start = max(arrival, time_to_minutes(joseph["start"]))
    end = start + joseph["duration"]
    if end > time_to_minutes(joseph["end"]):
        return None
    itinerary.append({
        "action": "meet",
        "location": joseph["location"],
        "person": joseph["name"],
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    })
    current_time = end
    current_location = joseph["location"]
    remaining_friends.remove(joseph)
    
    # Next, meet Karen (11:30-18:30)
    karen = next(f for f in remaining_friends if f["name"] == "Karen")
    travel = travel_times[current_location][karen["location"]]
    arrival = current_time + travel
    start = max(arrival, time_to_minutes(karen["start"]))
    end = start + karen["duration"]
    if end > time_to_minutes(karen["end"]):
        return None
    itinerary.append({
        "action": "meet",
        "location": karen["location"],
        "person": karen["name"],
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    })
    current_time = end
    current_location = karen["location"]
    remaining_friends.remove(karen)
    
    # Next, meet Brian (1:45-8:45)
    brian = next(f for f in remaining_friends if f["name"] == "Brian")
    travel = travel_times[current_location][brian["location"]]
    arrival = current_time + travel
    start = max(arrival, time_to_minutes(brian["start"]))
    end = start + brian["duration"]
    if end > time_to_minutes(brian["end"]):
        return None
    itinerary.append({
        "action": "meet",
        "location": brian["location"],
        "person": brian["name"],
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    })
    current_time = end
    current_location = brian["location"]
    remaining_friends.remove(brian)
    
    # Next, meet William (3:15-5:15)
    william = next(f for f in remaining_friends if f["name"] == "William")
    travel = travel_times[current_location][william["location"]]
    arrival = current_time + travel
    start = max(arrival, time_to_minutes(william["start"]))
    end = start + william["duration"]
    if end > time_to_minutes(william["end"]):
        return None
    itinerary.append({
        "action": "meet",
        "location": william["location"],
        "person": william["name"],
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    })
    current_time = end
    current_location = william["location"]
    remaining_friends.remove(william)
    
    # Next, meet David (4:45-7:15)
    david = next(f for f in remaining_friends if f["name"] == "David")
    travel = travel_times[current_location][david["location"]]
    arrival = current_time + travel
    start = max(arrival, time_to_minutes(david["start"]))
    end = start + david["duration"]
    if end > time_to_minutes(david["end"]):
        return None
    itinerary.append({
        "action": "meet",
        "location": david["location"],
        "person": david["name"],
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    })
    current_time = end
    current_location = david["location"]
    remaining_friends.remove(david)
    
    # Next, meet Matthew (5:15-7:15)
    matthew = next(f for f in remaining_friends if f["name"] == "Matthew")
    travel = travel_times[current_location][matthew["location"]]
    arrival = current_time + travel
    start = max(arrival, time_to_minutes(matthew["start"]))
    end = start + matthew["duration"]
    if end > time_to_minutes(matthew["end"]):
        return None
    itinerary.append({
        "action": "meet",
        "location": matthew["location"],
        "person": matthew["name"],
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    })
    current_time = end
    current_location = matthew["location"]
    remaining_friends.remove(matthew)
    
    # Next, meet Jeffrey (7:00-9:30)
    jeffrey = next(f for f in remaining_friends if f["name"] == "Jeffrey")
    travel = travel_times[current_location][jeffrey["location"]]
    arrival = current_time + travel
    start = max(arrival, time_to_minutes(jeffrey["start"]))
    end = start + jeffrey["duration"]
    if end > time_to_minutes(jeffrey["end"]):
        return None
    itinerary.append({
        "action": "meet",
        "location": jeffrey["location"],
        "person": jeffrey["name"],
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    })
    current_time = end
    current_location = jeffrey["location"]
    remaining_friends.remove(jeffrey)
    
    # Finally, meet Joshua (7:00-8:00PM)
    joshua = next(f for f in remaining_friends if f["name"] == "Joshua")
    travel = travel_times[current_location][joshua["location"]]
    arrival = current_time + travel
    start = max(arrival, time_to_minutes(joshua["start"]))
    end = start + joshua["duration"]
    if end > time_to_minutes(joshua["end"]):
        return None
    itinerary.append({
        "action": "meet",
        "location": joshua["location"],
        "person": joshua["name"],
        "start_time": minutes_to_time(start),
        "end_time": minutes_to_time(end)
    })
    
    return itinerary

best_itinerary = calculate_schedule()

if best_itinerary:
    result = {"itinerary": best_itinerary}
else:
    result = {"itinerary": []}

print(json.dumps(result, indent=2))