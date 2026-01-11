import json
from itertools import permutations

def time_to_minutes(t):
    """Convert '9:00AM' or '1:30PM' to minutes since midnight."""
    if 'AM' in t:
        t = t.replace('AM', '').strip()
        hour, minute = map(int, t.split(':'))
        if hour == 12:
            hour = 0
        return hour * 60 + minute
    elif 'PM' in t:
        t = t.replace('PM', '').strip()
        hour, minute = map(int, t.split(':'))
        if hour != 12:
            hour += 12
        return hour * 60 + minute
    else:
        raise ValueError(f"Time format unknown: {t}")

def minutes_to_time(m):
    """Convert minutes since midnight to 'H:MM' 24-hour format."""
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

# Travel times dictionary: travel_times[from_location][to_location] = minutes
travel_times = {
    "Marina District": {
        "Embarcadero": 14,
        "Bayview": 27,
        "Union Square": 16,
        "Chinatown": 15,
        "Sunset District": 19,
        "Golden Gate Park": 18,
        "Financial District": 17,
        "Haight-Ashbury": 16,
        "Mission District": 20,
    },
    "Embarcadero": {
        "Marina District": 12,
        "Bayview": 21,
        "Union Square": 10,
        "Chinatown": 7,
        "Sunset District": 30,
        "Golden Gate Park": 25,
        "Financial District": 5,
        "Haight-Ashbury": 21,
        "Mission District": 20,
    },
    "Bayview": {
        "Marina District": 27,
        "Embarcadero": 19,
        "Union Square": 18,
        "Chinatown": 19,
        "Sunset District": 23,
        "Golden Gate Park": 22,
        "Financial District": 19,
        "Haight-Ashbury": 19,
        "Mission District": 13,
    },
    "Union Square": {
        "Marina District": 18,
        "Embarcadero": 11,
        "Bayview": 15,
        "Chinatown": 7,
        "Sunset District": 27,
        "Golden Gate Park": 22,
        "Financial District": 9,
        "Haight-Ashbury": 18,
        "Mission District": 14,
    },
    "Chinatown": {
        "Marina District": 12,
        "Embarcadero": 5,
        "Bayview": 20,
        "Union Square": 7,
        "Sunset District": 29,
        "Golden Gate Park": 23,
        "Financial District": 5,
        "Haight-Ashbury": 19,
        "Mission District": 17,
    },
    "Sunset District": {
        "Marina District": 21,
        "Embarcadero": 30,
        "Bayview": 22,
        "Union Square": 30,
        "Chinatown": 30,
        "Golden Gate Park": 11,
        "Financial District": 30,
        "Haight-Ashbury": 15,
        "Mission District": 25,
    },
    "Golden Gate Park": {
        "Marina District": 16,
        "Embarcadero": 25,
        "Bayview": 23,
        "Union Square": 22,
        "Chinatown": 23,
        "Sunset District": 10,
        "Financial District": 26,
        "Haight-Ashbury": 7,
        "Mission District": 17,
    },
    "Financial District": {
        "Marina District": 15,
        "Embarcadero": 4,
        "Bayview": 19,
        "Union Square": 9,
        "Chinatown": 5,
        "Sunset District": 30,
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Mission District": 17,
    },
    "Haight-Ashbury": {
        "Marina District": 17,
        "Embarcadero": 20,
        "Bayview": 18,
        "Union Square": 19,
        "Chinatown": 19,
        "Sunset District": 15,
        "Golden Gate Park": 7,
        "Financial District": 21,
        "Mission District": 11,
    },
    "Mission District": {
        "Marina District": 19,
        "Embarcadero": 19,
        "Bayview": 14,
        "Union Square": 15,
        "Chinatown": 16,
        "Sunset District": 24,
        "Golden Gate Park": 17,
        "Financial District": 15,
        "Haight-Ashbury": 12,
    },
}

# Friends data: name -> (location, start_available, end_available, min_duration)
friends = {
    "Joshua": ("Embarcadero", time_to_minutes("9:45AM"), time_to_minutes("6:00PM"), 105),
    "Jeffrey": ("Bayview", time_to_minutes("9:45AM"), time_to_minutes("8:15PM"), 75),
    "Charles": ("Union Square", time_to_minutes("10:45AM"), time_to_minutes("8:15PM"), 120),
    "Joseph": ("Chinatown", time_to_minutes("7:00AM"), time_to_minutes("3:30PM"), 60),
    "Elizabeth": ("Sunset District", time_to_minutes("9:00AM"), time_to_minutes("9:45AM"), 45),
    "Matthew": ("Golden Gate Park", time_to_minutes("11:00AM"), time_to_minutes("7:30PM"), 45),
    "Carol": ("Financial District", time_to_minutes("10:45AM"), time_to_minutes("11:15AM"), 15),
    "Paul": ("Haight-Ashbury", time_to_minutes("7:15PM"), time_to_minutes("8:30PM"), 15),
    "Rebecca": ("Mission District", time_to_minutes("5:00PM"), time_to_minutes("9:45PM"), 45),
}

# Start at Marina District at 9:00 AM
start_time = time_to_minutes("9:00AM")
current_location = "Marina District"

def schedule_meetings(order):
    """Try to schedule meetings in given order, return itinerary if possible, else None."""
    itinerary = []
    current_loc = current_location
    current_time = start_time
    
    for name in order:
        loc, avail_start, avail_end, dur = friends[name]
        # Travel to loc
        travel = travel_times[current_loc][loc]
        arrival = current_time + travel
        # Start meeting at earliest possible time after arrival
        start_meeting = max(arrival, avail_start)
        if start_meeting + dur > avail_end:
            return None  # Cannot meet this friend in time
        end_meeting = start_meeting + dur
        itinerary.append((name, loc, start_meeting, end_meeting))
        current_time = end_meeting
        current_loc = loc
    return itinerary

# Try to meet all friends first
all_friends = list(friends.keys())
best_itinerary = None
best_count = 0

# Since trying all permutations is huge, we use a heuristic order:
# Elizabeth first (earliest end), then Carol (tight window), then others.
# We'll try a few reasonable permutations manually based on time windows.
# But for completeness, we'll do a limited search.

# Generate some likely orders based on time window endings
sorted_by_end = sorted(all_friends, key=lambda x: friends[x][2])
# We'll try a few permutations around this order
from itertools import islice

def try_orders():
    # Try Elizabeth first (only available 9:00-9:45)
    # Then Carol (10:45-11:15)
    # Then Joseph (ends 3:30PM)
    # Then others
    base_order = ["Elizabeth", "Carol", "Joseph", "Joshua", "Jeffrey", "Charles", "Matthew", "Rebecca", "Paul"]
    # Try variations
    variations = [
        ["Elizabeth", "Carol", "Joseph", "Joshua", "Charles", "Matthew", "Jeffrey", "Rebecca", "Paul"],
        ["Elizabeth", "Carol", "Joseph", "Charles", "Joshua", "Matthew", "Jeffrey", "Rebecca", "Paul"],
        ["Elizabeth", "Carol", "Joseph", "Joshua", "Matthew", "Charles", "Jeffrey", "Rebecca", "Paul"],
    ]
    for order in variations + [base_order]:
        itin = schedule_meetings(order)
        if itin:
            return itin, len(order)
    return None, 0

best_itinerary, best_count = try_orders()

# If can't meet all, try subsets
if best_itinerary is None:
    # Try meeting all except maybe the tight ones
    for size in range(len(all_friends), 0, -1):
        from itertools import combinations
        for subset in combinations(all_friends, size):
            # Try permutations of subset
            for perm in permutations(subset):
                itin = schedule_meetings(perm)
                if itin:
                    best_itinerary = itin
                    best_count = size
                    break
            if best_itinerary:
                break
        if best_itinerary:
            break

# Convert best itinerary to output format
output = {"itinerary": []}
if best_itinerary:
    for name, loc, start_m, end_m in best_itinerary:
        output["itinerary"].append({
            "action": "meet",
            "location": loc,
            "person": name,
            "start_time": minutes_to_time(start_m),
            "end_time": minutes_to_time(end_m)
        })

print(json.dumps(output, indent=2))