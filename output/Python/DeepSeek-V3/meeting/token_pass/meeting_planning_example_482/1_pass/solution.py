import json
from itertools import permutations
from datetime import datetime, timedelta

def parse_time(timestr):
    """Convert '9:00' or '13:30' to datetime today for easy math."""
    return datetime.strptime(timestr, "%H:%M")

def format_time(dt):
    """Convert datetime to 'H:MM' or 'HH:MM' without leading zero for hour."""
    return dt.strftime("%-H:%M")

def add_minutes(dt, minutes):
    return dt + timedelta(minutes=minutes)

# Travel times matrix: from_index to to_index in minutes
locations = ["Haight-Ashbury", "Mission District", "Bayview", "Pacific Heights", "Russian Hill", "Fisherman's Wharf"]
loc_index = {loc: i for i, loc in enumerate(locations)}

# Asymmetric travel times [from][to]
travel = [
    [0, 11, 18, 12, 17, 23],  # Haight-Ashbury
    [12, 0, 15, 16, 15, 22],  # Mission District
    [19, 13, 0, 23, 23, 25],  # Bayview
    [11, 15, 22, 0, 7, 13],   # Pacific Heights
    [17, 16, 23, 7, 0, 7],    # Russian Hill
    [22, 22, 26, 12, 7, 0]    # Fisherman's Wharf
]

# Friend data: name, location, available_start, available_end, min_duration (minutes)
friends = [
    ("Stephanie", "Mission District", "8:15", "13:45", 90),
    ("Sandra", "Bayview", "13:00", "19:30", 15),
    ("Richard", "Pacific Heights", "7:15", "10:15", 75),
    ("Brian", "Russian Hill", "12:15", "16:00", 120),
    ("Jason", "Fisherman's Wharf", "8:30", "17:45", 60)
]

# Remove Richard because impossible from start
friends = [f for f in friends if f[0] != "Richard"]

start_loc = "Haight-Ashbury"
start_time = parse_time("9:00")

best_itinerary = []
best_count = 0

# Try all permutations of remaining 4 friends
for perm in permutations(friends):
    current_time = start_time
    current_loc = start_loc
    itinerary = []
    possible = True
    
    for name, loc, avail_start_str, avail_end_str, min_dur in perm:
        travel_time = travel[loc_index[current_loc]][loc_index[loc]]
        arrive_time = add_minutes(current_time, travel_time)
        avail_start = parse_time(avail_start_str)
        avail_end = parse_time(avail_end_str)
        
        # If arrive before available start, wait
        if arrive_time < avail_start:
            arrive_time = avail_start
        
        # Check if we can meet for min_dur before avail_end
        if add_minutes(arrive_time, min_dur) > avail_end:
            possible = False
            break
        
        # Schedule meeting
        meeting_end = add_minutes(arrive_time, min_dur)
        itinerary.append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": format_time(arrive_time),
            "end_time": format_time(meeting_end)
        })
        
        current_time = meeting_end
        current_loc = loc
    
    if possible and len(itinerary) > best_count:
        best_count = len(itinerary)
        best_itinerary = itinerary

# Output result
result = {"itinerary": best_itinerary}
print(json.dumps(result, indent=2))