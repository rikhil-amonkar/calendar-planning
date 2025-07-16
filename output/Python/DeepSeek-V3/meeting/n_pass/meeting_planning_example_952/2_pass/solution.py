import json
from itertools import permutations

# Travel times dictionary
travel_times = {
    "Bayview": {
        "North Beach": 22, "Fisherman's Wharf": 25, "Haight-Ashbury": 19,
        "Nob Hill": 20, "Golden Gate Park": 22, "Union Square": 18,
        "Alamo Square": 16, "Presidio": 32, "Chinatown": 19, "Pacific Heights": 23
    },
    "North Beach": {
        "Bayview": 25, "Fisherman's Wharf": 5, "Haight-Ashbury": 18,
        "Nob Hill": 7, "Golden Gate Park": 22, "Union Square": 7,
        "Alamo Square": 16, "Presidio": 17, "Chinatown": 6, "Pacific Heights": 8
    },
    "Fisherman's Wharf": {
        "Bayview": 26, "North Beach": 6, "Haight-Ashbury": 22,
        "Nob Hill": 11, "Golden Gate Park": 25, "Union Square": 13,
        "Alamo Square": 21, "Presidio": 17, "Chinatown": 12, "Pacific Heights": 12
    },
    "Haight-Ashbury": {
        "Bayview": 18, "North Beach": 19, "Fisherman's Wharf": 23,
        "Nob Hill": 15, "Golden Gate Park": 7, "Union Square": 19,
        "Alamo Square": 5, "Presidio": 15, "Chinatown": 19, "Pacific Heights": 12
    },
    "Nob Hill": {
        "Bayview": 19, "North Beach": 8, "Fisherman's Wharf": 10,
        "Haight-Ashbury": 13, "Golden Gate Park": 17, "Union Square": 7,
        "Alamo Square": 11, "Presidio": 17, "Chinatown": 6, "Pacific Heights": 8
    },
    "Golden Gate Park": {
        "Bayview": 23, "North Beach": 23, "Fisherman's Wharf": 24,
        "Haight-Ashbury": 7, "Nob Hill": 20, "Union Square": 22,
        "Alamo Square": 9, "Presidio": 11, "Chinatown": 23, "Pacific Heights": 16
    },
    "Union Square": {
        "Bayview": 15, "North Beach": 10, "Fisherman's Wharf": 15,
        "Haight-Ashbury": 18, "Nob Hill": 9, "Golden Gate Park": 22,
        "Alamo Square": 15, "Presidio": 24, "Chinatown": 7, "Pacific Heights": 15
    },
    "Alamo Square": {
        "Bayview": 16, "North Beach": 15, "Fisherman's Wharf": 19,
        "Haight-Ashbury": 5, "Nob Hill": 11, "Golden Gate Park": 9,
        "Union Square": 14, "Presidio": 17, "Chinatown": 15, "Pacific Heights": 10
    },
    "Presidio": {
        "Bayview": 31, "North Beach": 18, "Fisherman's Wharf": 19,
        "Haight-Ashbury": 15, "Nob Hill": 18, "Golden Gate Park": 12,
        "Union Square": 22, "Alamo Square": 19, "Chinatown": 21, "Pacific Heights": 11
    },
    "Chinatown": {
        "Bayview": 20, "North Beach": 3, "Fisherman's Wharf": 8,
        "Haight-Ashbury": 19, "Nob Hill": 9, "Golden Gate Park": 23,
        "Union Square": 7, "Alamo Square": 17, "Presidio": 19, "Pacific Heights": 10
    },
    "Pacific Heights": {
        "Bayview": 22, "North Beach": 9, "Fisherman's Wharf": 13,
        "Haight-Ashbury": 11, "Nob Hill": 8, "Golden Gate Park": 15,
        "Union Square": 12, "Alamo Square": 10, "Presidio": 11, "Chinatown": 11
    }
}

# Friend data
friends = [
    {"name": "Matthew", "location": "Presidio", "start": "8:15", "end": "9:00", "duration": 15},
    {"name": "Richard", "location": "Fisherman's Wharf", "start": "11:00", "end": "12:45", "duration": 60},
    {"name": "Elizabeth", "location": "Nob Hill", "start": "11:45", "end": "6:30", "duration": 75},
    {"name": "Anthony", "location": "Pacific Heights", "start": "2:15", "end": "4:00", "duration": 30},
    {"name": "Brian", "location": "North Beach", "start": "1:00", "end": "7:00", "duration": 90},
    {"name": "Kenneth", "location": "Chinatown", "start": "1:45", "end": "7:30", "duration": 105},
    {"name": "Ashley", "location": "Haight-Ashbury", "start": "3:00", "end": "8:30", "duration": 90},
    {"name": "Kimberly", "location": "Alamo Square", "start": "5:30", "end": "9:15", "duration": 45},
    {"name": "Deborah", "location": "Union Square", "start": "5:30", "end": "10:00", "duration": 60},
    {"name": "Jessica", "location": "Golden Gate Park", "start": "8:00", "end": "9:45", "duration": 105}
]

def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def can_meet(current_time, friend, current_location):
    start = time_to_minutes(friend["start"])
    end = time_to_minutes(friend["end"])
    travel_time = travel_times[current_location][friend["location"]]
    arrival_time = current_time + travel_time
    
    # Check if we can arrive before the window ends
    if arrival_time > end:
        return None
        
    # Earliest we can start meeting (max of arrival time or friend's start time)
    meet_start = max(arrival_time, start)
    meet_end = meet_start + friend["duration"]
    
    # Check if meeting fits in friend's window
    if meet_end > end:
        return None
        
    return (meet_start, meet_end)

def evaluate_schedule(order):
    current_time = time_to_minutes("9:00")  # Starting at 9:00 from Bayview
    current_location = "Bayview"
    schedule = []
    
    for friend in order:
        result = can_meet(current_time, friend, current_location)
        if result is None:
            continue  # Skip this friend but continue with the schedule
            
        meet_start, meet_end = result
        schedule.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": minutes_to_time(meet_start),
            "end_time": minutes_to_time(meet_end)
        })
        current_time = meet_end
        current_location = friend["location"]
        
    return schedule

def generate_possible_orders(friends, max_permutations=10000):
    # Prioritize friends with earlier end times first
    sorted_friends = sorted(friends, key=lambda x: time_to_minutes(x["end"]))
    
    # Try all possible subsets from size 1 to 10
    for i in range(1, len(sorted_friends) + 1):
        count = 0
        for perm in permutations(sorted_friends, i):
            if count >= max_permutations:
                break
            yield list(perm)
            count += 1

best_schedule = None
best_count = 0

for order in generate_possible_orders(friends):
    schedule = evaluate_schedule(order)
    if schedule and len(schedule) > best_count:
        best_schedule = schedule
        best_count = len(schedule)
        # Early exit if we found the maximum possible
        if best_count == len(friends):
            break

if best_schedule is None:
    result = {"itinerary": []}
else:
    result = {"itinerary": best_schedule}

print(json.dumps(result, indent=2))