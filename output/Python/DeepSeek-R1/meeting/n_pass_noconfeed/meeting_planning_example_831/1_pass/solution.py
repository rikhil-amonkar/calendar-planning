import itertools
import json

def time_to_minutes(time_str):
    period = time_str[-2:]
    time_part = time_str[:-2].strip()
    parts = time_part.split(':')
    hour = int(parts[0])
    minute = int(parts[1])
    if period == 'AM':
        if hour == 12:
            hour = 0
    else:  # PM
        if hour != 12:
            hour += 12
    return hour * 60 + minute

def format_time(minutes_since_midnight):
    hours = minutes_since_midnight // 60
    minutes = minutes_since_midnight % 60
    return f"{hours}:{minutes:02d}"

# Travel times dictionary
travel_times = {
    "Presidio": {
        "Fisherman's Wharf": 19,
        "Alamo Square": 19,
        "Financial District": 23,
        "Union Square": 22,
        "Sunset District": 15,
        "Embarcadero": 20,
        "Golden Gate Park": 12,
        "Chinatown": 21,
        "Richmond District": 7
    },
    "Fisherman's Wharf": {
        "Presidio": 17,
        "Alamo Square": 21,
        "Financial District": 11,
        "Union Square": 13,
        "Sunset District": 27,
        "Embarcadero": 8,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Richmond District": 18
    },
    "Alamo Square": {
        "Presidio": 17,
        "Fisherman's Wharf": 19,
        "Financial District": 17,
        "Union Square": 14,
        "Sunset District": 16,
        "Embarcadero": 16,
        "Golden Gate Park": 9,
        "Chinatown": 15,
        "Richmond District": 11
    },
    "Financial District": {
        "Presidio": 22,
        "Fisherman's Wharf": 10,
        "Alamo Square": 17,
        "Union Square": 9,
        "Sunset District": 30,
        "Embarcadero": 4,
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Richmond District": 21
    },
    "Union Square": {
        "Presidio": 24,
        "Fisherman's Wharf": 15,
        "Alamo Square": 15,
        "Financial District": 9,
        "Sunset District": 27,
        "Embarcadero": 11,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Richmond District": 20
    },
    "Sunset District": {
        "Presidio": 16,
        "Fisherman's Wharf": 29,
        "Alamo Square": 17,
        "Financial District": 30,
        "Union Square": 30,
        "Embarcadero": 30,
        "Golden Gate Park": 11,
        "Chinatown": 30,
        "Richmond District": 12
    },
    "Embarcadero": {
        "Presidio": 20,
        "Fisherman's Wharf": 6,
        "Alamo Square": 19,
        "Financial District": 5,
        "Union Square": 10,
        "Sunset District": 30,
        "Golden Gate Park": 25,
        "Chinatown": 7,
        "Richmond District": 21
    },
    "Golden Gate Park": {
        "Presidio": 11,
        "Fisherman's Wharf": 24,
        "Alamo Square": 9,
        "Financial District": 26,
        "Union Square": 22,
        "Sunset District": 10,
        "Embarcadero": 25,
        "Chinatown": 23,
        "Richmond District": 7
    },
    "Chinatown": {
        "Presidio": 19,
        "Fisherman's Wharf": 8,
        "Alamo Square": 17,
        "Financial District": 5,
        "Union Square": 7,
        "Sunset District": 29,
        "Embarcadero": 5,
        "Golden Gate Park": 23,
        "Richmond District": 20
    },
    "Richmond District": {
        "Presidio": 7,
        "Fisherman's Wharf": 18,
        "Alamo Square": 13,
        "Financial District": 22,
        "Union Square": 21,
        "Sunset District": 11,
        "Embarcadero": 19,
        "Golden Gate Park": 9,
        "Chinatown": 20
    }
}

# Define friends with their constraints
friends = [
    {"name": "Jeffrey", "location": "Fisherman's Wharf", "available_start": time_to_minutes("10:15AM"), "available_end": time_to_minutes("1:00PM"), "min_duration": 90},
    {"name": "Ronald", "location": "Alamo Square", "available_start": time_to_minutes("7:45AM"), "available_end": time_to_minutes("2:45PM"), "min_duration": 120},
    {"name": "Jason", "location": "Financial District", "available_start": time_to_minutes("10:45AM"), "available_end": time_to_minutes("4:00PM"), "min_duration": 105},
    {"name": "Melissa", "location": "Union Square", "available_start": time_to_minutes("5:45PM"), "available_end": time_to_minutes("6:15PM"), "min_duration": 15},
    {"name": "Elizabeth", "location": "Sunset District", "available_start": time_to_minutes("2:45PM"), "available_end": time_to_minutes("5:30PM"), "min_duration": 105},
    {"name": "Margaret", "location": "Embarcadero", "available_start": time_to_minutes("1:15PM"), "available_end": time_to_minutes("7:00PM"), "min_duration": 90},
    {"name": "George", "location": "Golden Gate Park", "available_start": time_to_minutes("7:00PM"), "available_end": time_to_minutes("10:00PM"), "min_duration": 75},
    {"name": "Richard", "location": "Chinatown", "available_start": time_to_minutes("9:30AM"), "available_end": time_to_minutes("9:00PM"), "min_duration": 15},
    {"name": "Laura", "location": "Richmond District", "available_start": time_to_minutes("9:45AM"), "available_end": time_to_minutes("6:00PM"), "min_duration": 60}
]

def is_feasible(perm, travel_times, start_time, start_location):
    current_time = start_time
    current_location = start_location
    schedule_details = []
    for friend in perm:
        travel_time = travel_times[current_location][friend["location"]]
        arrival_time = current_time + travel_time
        meeting_start = max(arrival_time, friend["available_start"])
        if meeting_start + friend["min_duration"] > friend["available_end"]:
            return False, None
        meeting_end = meeting_start + friend["min_duration"]
        current_time = meeting_end
        current_location = friend["location"]
        schedule_details.append((friend, meeting_start, meeting_end))
    return True, schedule_details

start_time_abs = time_to_minutes("9:00AM")  # 540 minutes (9:00 AM)
start_location = "Presidio"
best_schedule = None
best_count = 0

# Try from r=9 down to 1
n = len(friends)
for r in range(n, 0, -1):
    found = False
    for subset in itertools.combinations(friends, r):
        for perm in itertools.permutations(subset):
            feasible, schedule_details = is_feasible(perm, travel_times, start_time_abs, start_location)
            if feasible:
                best_schedule = schedule_details
                best_count = r
                found = True
                break
        if found:
            break
    if found:
        break

# Format the result
itinerary = []
if best_schedule is not None:
    for friend, start_abs, end_abs in best_schedule:
        itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": format_time(start_abs),
            "end_time": format_time(end_abs)
        })

# Output as JSON
result = {"itinerary": itinerary}
print(json.dumps(result))