import json
import itertools
from collections import defaultdict

def time_to_minutes(t):
    """Convert 'H:MMAM/PM' to minutes since midnight."""
    if isinstance(t, str):
        if 'AM' in t or 'PM' in t:
            parts = t.replace('AM', '').replace('PM', '').strip().split(':')
            h = int(parts[0])
            m = int(parts[1])
            if 'PM' in t and h != 12:
                h += 12
            if 'AM' in t and h == 12:
                h = 0
            return h * 60 + m
        else:
            # Already in H:MM 24h format
            h, m = map(int, t.split(':'))
            return h * 60 + m
    return t

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' 24h format."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times matrix (in minutes)
districts = [
    "Marina District", "Mission District", "Fisherman's Wharf", "Presidio",
    "Union Square", "Sunset District", "Financial District", "Haight-Ashbury", "Russian Hill"
]

# Build travel time dictionary
travel_raw = [
    ("Marina District", "Mission District", 20),
    ("Marina District", "Fisherman's Wharf", 10),
    ("Marina District", "Presidio", 10),
    ("Marina District", "Union Square", 16),
    ("Marina District", "Sunset District", 19),
    ("Marina District", "Financial District", 17),
    ("Marina District", "Haight-Ashbury", 16),
    ("Marina District", "Russian Hill", 8),
    ("Mission District", "Marina District", 19),
    ("Mission District", "Fisherman's Wharf", 22),
    ("Mission District", "Presidio", 25),
    ("Mission District", "Union Square", 15),
    ("Mission District", "Sunset District", 24),
    ("Mission District", "Financial District", 15),
    ("Mission District", "Haight-Ashbury", 12),
    ("Mission District", "Russian Hill", 15),
    ("Fisherman's Wharf", "Marina District", 9),
    ("Fisherman's Wharf", "Mission District", 22),
    ("Fisherman's Wharf", "Presidio", 17),
    ("Fisherman's Wharf", "Union Square", 13),
    ("Fisherman's Wharf", "Sunset District", 27),
    ("Fisherman's Wharf", "Financial District", 11),
    ("Fisherman's Wharf", "Haight-Ashbury", 22),
    ("Fisherman's Wharf", "Russian Hill", 7),
    ("Presidio", "Marina District", 11),
    ("Presidio", "Mission District", 26),
    ("Presidio", "Fisherman's Wharf", 19),
    ("Presidio", "Union Square", 22),
    ("Presidio", "Sunset District", 15),
    ("Presidio", "Financial District", 23),
    ("Presidio", "Haight-Ashbury", 15),
    ("Presidio", "Russian Hill", 14),
    ("Union Square", "Marina District", 18),
    ("Union Square", "Mission District", 14),
    ("Union Square", "Fisherman's Wharf", 15),
    ("Union Square", "Presidio", 24),
    ("Union Square", "Sunset District", 27),
    ("Union Square", "Financial District", 9),
    ("Union Square", "Haight-Ashbury", 18),
    ("Union Square", "Russian Hill", 13),
    ("Sunset District", "Marina District", 21),
    ("Sunset District", "Mission District", 25),
    ("Sunset District", "Fisherman's Wharf", 29),
    ("Sunset District", "Presidio", 16),
    ("Sunset District", "Union Square", 30),
    ("Sunset District", "Financial District", 30),
    ("Sunset District", "Haight-Ashbury", 15),
    ("Sunset District", "Russian Hill", 24),
    ("Financial District", "Marina District", 15),
    ("Financial District", "Mission District", 17),
    ("Financial District", "Fisherman's Wharf", 10),
    ("Financial District", "Presidio", 22),
    ("Financial District", "Union Square", 9),
    ("Financial District", "Sunset District", 30),
    ("Financial District", "Haight-Ashbury", 19),
    ("Financial District", "Russian Hill", 11),
    ("Haight-Ashbury", "Marina District", 17),
    ("Haight-Ashbury", "Mission District", 11),
    ("Haight-Ashbury", "Fisherman's Wharf", 23),
    ("Haight-Ashbury", "Presidio", 15),
    ("Haight-Ashbury", "Union Square", 19),
    ("Haight-Ashbury", "Sunset District", 15),
    ("Haight-Ashbury", "Financial District", 21),
    ("Haight-Ashbury", "Russian Hill", 17),
    ("Russian Hill", "Marina District", 7),
    ("Russian Hill", "Mission District", 16),
    ("Russian Hill", "Fisherman's Wharf", 7),
    ("Russian Hill", "Presidio", 14),
    ("Russian Hill", "Union Square", 10),
    ("Russian Hill", "Sunset District", 23),
    ("Russian Hill", "Financial District", 11),
    ("Russian Hill", "Haight-Ashbury", 17),
]

travel = defaultdict(dict)
for a, b, t in travel_raw:
    travel[a][b] = t

# Friends data: name, location, window start, window end, min_duration (minutes)
friends = [
    ("Karen", "Mission District", "14:15", "22:00", 30),
    ("Richard", "Fisherman's Wharf", "14:30", "17:30", 30),
    ("Robert", "Presidio", "21:45", "22:45", 60),
    ("Joseph", "Union Square", "11:45", "14:45", 120),
    ("Helen", "Sunset District", "14:45", "20:45", 105),
    ("Elizabeth", "Financial District", "10:00", "12:45", 75),
    ("Kimberly", "Haight-Ashbury", "14:15", "17:30", 105),
    ("Ashley", "Russian Hill", "11:30", "21:30", 45),
]

# Convert to minutes since midnight
friends_m = []
for name, loc, start, end, dur in friends:
    friends_m.append({
        "name": name,
        "location": loc,
        "start": time_to_minutes(start),
        "end": time_to_minutes(end),
        "min_dur": dur
    })

# Start state
start_loc = "Marina District"
start_time = time_to_minutes("9:00")

# Search over all permutations
best_meetings = 0
best_total_time = 0
best_schedule = []

for perm in itertools.permutations(friends_m):
    current_loc = start_loc
    current_time = start_time
    schedule = []
    meetings = 0
    total_meeting_time = 0
    
    for friend in perm:
        # Travel to friend's location
        travel_time = travel[current_loc][friend["location"]]
        arrival = current_time + travel_time
        
        # Find earliest start time within friend's window
        # Start at max(arrival, friend["start"])
        start_meeting = max(arrival, friend["start"])
        # Check if we can meet for min_duration before friend["end"]
        if start_meeting + friend["min_dur"] <= friend["end"]:
            # Schedule meeting
            end_meeting = start_meeting + friend["min_dur"]
            schedule.append({
                "name": friend["name"],
                "loc": friend["location"],
                "start": start_meeting,
                "end": end_meeting
            })
            meetings += 1
            total_meeting_time += friend["min_dur"]
            current_loc = friend["location"]
            current_time = end_meeting
        else:
            # Cannot meet this friend in this permutation
            continue
    
    # Evaluate
    if meetings > best_meetings or (meetings == best_meetings and total_meeting_time > best_total_time):
        best_meetings = meetings
        best_total_time = total_meeting_time
        best_schedule = schedule

# Convert best_schedule to required JSON format
itinerary = []
for meet in best_schedule:
    itinerary.append({
        "action": "meet",
        "location": meet["loc"],
        "person": meet["name"],
        "start_time": minutes_to_time(meet["start"]),
        "end_time": minutes_to_time(meet["end"])
    })

result = {"itinerary": itinerary}
print(json.dumps(result, indent=2))