import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

travel_times = {
    "Presidio": {
        "Marina District": 11,
        "The Castro": 21,
        "Fisherman's Wharf": 19,
        "Bayview": 31,
        "Pacific Heights": 11,
        "Mission District": 26,
        "Alamo Square": 19,
        "Golden Gate Park": 12
    },
    "Marina District": {
        "Presidio": 10,
        "The Castro": 22,
        "Fisherman's Wharf": 10,
        "Bayview": 27,
        "Pacific Heights": 7,
        "Mission District": 20,
        "Alamo Square": 15,
        "Golden Gate Park": 18
    },
    "The Castro": {
        "Presidio": 20,
        "Marina District": 21,
        "Fisherman's Wharf": 24,
        "Bayview": 19,
        "Pacific Heights": 16,
        "Mission District": 7,
        "Alamo Square": 8,
        "Golden Gate Park": 11
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Marina District": 9,
        "The Castro": 27,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Mission District": 22,
        "Alamo Square": 21,
        "Golden Gate Park": 25
    },
    "Bayview": {
        "Presidio": 32,
        "Marina District": 27,
        "The Castro": 19,
        "Fisherman's Wharf": 25,
        "Pacific Heights": 23,
        "Mission District": 13,
        "Alamo Square": 16,
        "Golden Gate Park": 22
    },
    "Pacific Heights": {
        "Presidio": 11,
        "Marina District": 6,
        "The Castro": 16,
        "Fisherman's Wharf": 13,
        "Bayview": 22,
        "Mission District": 15,
        "Alamo Square": 10,
        "Golden Gate Park": 15
    },
    "Mission District": {
        "Presidio": 25,
        "Marina District": 19,
        "The Castro": 7,
        "Fisherman's Wharf": 22,
        "Bayview": 14,
        "Pacific Heights": 16,
        "Alamo Square": 11,
        "Golden Gate Park": 17
    },
    "Alamo Square": {
        "Presidio": 17,
        "Marina District": 15,
        "The Castro": 8,
        "Fisherman's Wharf": 19,
        "Bayview": 16,
        "Pacific Heights": 10,
        "Mission District": 10,
        "Golden Gate Park": 9
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Marina District": 16,
        "The Castro": 13,
        "Fisherman's Wharf": 24,
        "Bayview": 23,
        "Pacific Heights": 16,
        "Mission District": 17,
        "Alamo Square": 9
    }
}

friends = [
    {
        "name": "Amanda",
        "location": "Marina District",
        "start": "14:45",
        "end": "19:30",
        "duration": 105
    },
    {
        "name": "Melissa",
        "location": "The Castro",
        "start": "9:30",
        "end": "17:00",
        "duration": 30
    },
    {
        "name": "Jeffrey",
        "location": "Fisherman's Wharf",
        "start": "12:45",
        "end": "18:45",
        "duration": 120
    },
    {
        "name": "Matthew",
        "location": "Bayview",
        "start": "10:15",
        "end": "13:15",
        "duration": 30
    },
    {
        "name": "Nancy",
        "location": "Pacific Heights",
        "start": "17:00",
        "end": "21:30",
        "duration": 105
    },
    {
        "name": "Karen",
        "location": "Mission District",
        "start": "17:30",
        "end": "20:30",
        "duration": 105
    },
    {
        "name": "Robert",
        "location": "Alamo Square",
        "start": "11:15",
        "end": "17:30",
        "duration": 120
    },
    {
        "name": "Joseph",
        "location": "Golden Gate Park",
        "start": "8:30",
        "end": "21:15",
        "duration": 105
    }
]

def generate_schedule(order):
    current_time = time_to_minutes("9:00")
    current_location = "Presidio"
    schedule = []
    met_friends = set()
    
    for friend_name in order:
        friend = next(f for f in friends if f["name"] == friend_name)
        location = friend["location"]
        
        travel_time = travel_times[current_location].get(location, float('inf'))
        arrival_time = current_time + travel_time
        
        window_start = time_to_minutes(friend["start"])
        window_end = time_to_minutes(friend["end"])
        
        if arrival_time < window_start:
            arrival_time = window_start
        
        meeting_end = arrival_time + friend["duration"]
        if meeting_end > window_end:
            continue
        
        schedule.append({
            "action": "meet",
            "location": location,
            "person": friend["name"],
            "start_time": minutes_to_time(arrival_time),
            "end_time": minutes_to_time(meeting_end)
        })
        met_friends.add(friend["name"])
        current_time = meeting_end
        current_location = location
    
    return schedule, len(met_friends)

# Prioritize friends with tighter windows first
priority_order = ["Melissa", "Matthew", "Robert", "Jeffrey", "Amanda", "Karen", "Nancy", "Joseph"]

best_schedule = []
max_friends = 0

# First try to include all friends with Karen
for perm in permutations(priority_order):
    if "Karen" not in perm:
        continue
    schedule, num_friends = generate_schedule(perm)
    if num_friends > max_friends:
        max_friends = num_friends
        best_schedule = schedule
    if max_friends == len(friends):
        break

# If we couldn't meet all, try to maximize with Karen included
if max_friends < len(friends):
    # Try all possible subsets that include Karen
    from itertools import combinations
    friend_names = [f["name"] for f in friends]
    for size in range(len(friends), 0, -1):
        for combo in combinations(friend_names, size):
            if "Karen" not in combo:
                continue
            for perm in permutations(combo):
                schedule, num_friends = generate_schedule(perm)
                if num_friends > max_friends:
                    max_friends = num_friends
                    best_schedule = schedule
                    if max_friends == size:  # Can't do better for this size
                        break
            if max_friends == size:
                break
        if max_friends > 0:  # Found at least one valid schedule with Karen
            break

output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))