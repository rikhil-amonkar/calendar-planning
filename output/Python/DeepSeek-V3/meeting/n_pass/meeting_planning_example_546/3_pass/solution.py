import json
from itertools import permutations

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

# Input parameters
friends = [
    {"name": "Kenneth", "location": "Richmond District", "available_start": "21:15", "available_end": "22:00", "min_duration": 30},
    {"name": "Lisa", "location": "Union Square", "available_start": "9:00", "available_end": "16:30", "min_duration": 45},
    {"name": "Joshua", "location": "Financial District", "available_start": "12:00", "available_end": "15:15", "min_duration": 15},
    {"name": "Nancy", "location": "Pacific Heights", "available_start": "8:00", "available_end": "11:30", "min_duration": 90},
    {"name": "Andrew", "location": "Nob Hill", "available_start": "11:30", "available_end": "20:15", "min_duration": 60},
    {"name": "John", "location": "Bayview", "available_start": "16:45", "available_end": "21:30", "min_duration": 75}
]

travel_times = {
    "Embarcadero": {
        "Richmond District": 21,
        "Union Square": 10,
        "Financial District": 5,
        "Pacific Heights": 11,
        "Nob Hill": 10,
        "Bayview": 21
    },
    "Richmond District": {
        "Embarcadero": 19,
        "Union Square": 21,
        "Financial District": 22,
        "Pacific Heights": 10,
        "Nob Hill": 17,
        "Bayview": 26
    },
    "Union Square": {
        "Embarcadero": 11,
        "Richmond District": 20,
        "Financial District": 9,
        "Pacific Heights": 15,
        "Nob Hill": 9,
        "Bayview": 15
    },
    "Financial District": {
        "Embarcadero": 4,
        "Richmond District": 21,
        "Union Square": 9,
        "Pacific Heights": 13,
        "Nob Hill": 8,
        "Bayview": 19
    },
    "Pacific Heights": {
        "Embarcadero": 10,
        "Richmond District": 12,
        "Union Square": 12,
        "Financial District": 13,
        "Nob Hill": 8,
        "Bayview": 22
    },
    "Nob Hill": {
        "Embarcadero": 9,
        "Richmond District": 14,
        "Union Square": 7,
        "Financial District": 9,
        "Pacific Heights": 8,
        "Bayview": 19
    },
    "Bayview": {
        "Embarcadero": 19,
        "Richmond District": 25,
        "Union Square": 17,
        "Financial District": 19,
        "Pacific Heights": 23,
        "Nob Hill": 20
    }
}

def get_travel_time(from_loc, to_loc):
    return travel_times.get(from_loc, {}).get(to_loc, float('inf'))

def evaluate_schedule(order):
    current_time = time_to_minutes("8:00")
    current_location = "Embarcadero"
    itinerary = []
    met_friends = set()
    
    for friend in order:
        name = friend["name"]
        location = friend["location"]
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]
        
        # Travel to friend's location
        travel_time = get_travel_time(current_location, location)
        arrival_time = current_time + travel_time
        
        # Check if we can meet the friend
        meeting_start = max(arrival_time, available_start)
        meeting_end = meeting_start + min_duration
        
        if meeting_end > available_end:
            return 0, []  # Can't meet this friend in this order
        
        # Add to itinerary
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": name,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        })
        
        met_friends.add(name)
        current_time = meeting_end
        current_location = location
    
    return len(met_friends), itinerary

# Generate all possible orders of friends (including Kenneth)
best_met = 0
best_itinerary = []

# Try all permutations of all friends
for order in permutations(friends, len(friends)):
    met, itinerary = evaluate_schedule(order)
    if met > best_met or (met == best_met and len(itinerary) > len(best_itinerary)):
        best_met = met
        best_itinerary = itinerary
        if best_met == len(friends):  # Found optimal solution
            break

# Output the best itinerary
output = {
    "itinerary": best_itinerary
}

print(json.dumps(output, indent=2))