import json
from itertools import permutations

# Travel times dictionary (from -> to -> minutes)
travel_times = {
    "Financial District": {
        "Golden Gate Park": 23,
        "Chinatown": 5,
        "Union Square": 9,
        "Fisherman's Wharf": 10,
        "Pacific Heights": 13,
        "North Beach": 7
    },
    "Golden Gate Park": {
        "Financial District": 26,
        "Chinatown": 23,
        "Union Square": 22,
        "Fisherman's Wharf": 24,
        "Pacific Heights": 16,
        "North Beach": 24
    },
    "Chinatown": {
        "Financial District": 5,
        "Golden Gate Park": 23,
        "Union Square": 7,
        "Fisherman's Wharf": 8,
        "Pacific Heights": 10,
        "North Beach": 3
    },
    "Union Square": {
        "Financial District": 9,
        "Golden Gate Park": 22,
        "Chinatown": 7,
        "Fisherman's Wharf": 15,
        "Pacific Heights": 15,
        "North Beach": 10
    },
    "Fisherman's Wharf": {
        "Financial District": 11,
        "Golden Gate Park": 25,
        "Chinatown": 12,
        "Union Square": 13,
        "Pacific Heights": 12,
        "North Beach": 6
    },
    "Pacific Heights": {
        "Financial District": 13,
        "Golden Gate Park": 15,
        "Chinatown": 11,
        "Union Square": 12,
        "Fisherman's Wharf": 13,
        "North Beach": 9
    },
    "North Beach": {
        "Financial District": 8,
        "Golden Gate Park": 22,
        "Chinatown": 6,
        "Union Square": 7,
        "Fisherman's Wharf": 5,
        "Pacific Heights": 8
    }
}

# Convert time string to minutes since midnight
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(':'))
    return h * 60 + m

# Convert minutes to time string
def minutes_to_time(m):
    return f"{m // 60}:{m % 60:02d}"

# Friends data: name -> (location, start, end, min_duration)
friends = {
    "Stephanie": ("Golden Gate Park", time_to_minutes("11:00"), time_to_minutes("15:00"), 105),
    "Karen": ("Chinatown", time_to_minutes("13:45"), time_to_minutes("16:30"), 15),
    "Brian": ("Union Square", time_to_minutes("15:00"), time_to_minutes("17:15"), 30),
    "Rebecca": ("Fisherman's Wharf", time_to_minutes("8:00"), time_to_minutes("11:15"), 30),
    "Joseph": ("Pacific Heights", time_to_minutes("8:15"), time_to_minutes("9:30"), 60),
    "Steven": ("North Beach", time_to_minutes("14:30"), time_to_minutes("20:45"), 120)
}

def calculate_schedule(order):
    current_time = time_to_minutes("9:00")  # Start at Financial District at 9:00
    current_location = "Financial District"
    schedule = []
    met_friends = set()
    
    for friend in order:
        location, friend_start, friend_end, min_duration = friends[friend]
        
        # Calculate travel time
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        
        # Check if we can meet this friend
        meet_start = max(arrival_time, friend_start)
        meet_end = min(meet_start + min_duration, friend_end)
        
        if meet_end - meet_start >= min_duration:
            schedule.append({
                "action": "meet",
                "location": location,
                "person": friend,
                "start_time": minutes_to_time(meet_start),
                "end_time": minutes_to_time(meet_end)
            })
            met_friends.add(friend)
            current_time = meet_end
            current_location = location
        else:
            # Can't meet this friend in this order
            return None, set()
    
    return schedule, met_friends

def find_optimal_schedule():
    best_schedule = None
    max_met = 0
    
    # Try all possible orders of friends (but limit to 6 friends for performance)
    for order in permutations(friends.keys()):
        schedule, met_friends = calculate_schedule(order)
        if schedule is not None:  # Only consider valid schedules
            if len(met_friends) > max_met or (len(met_friends) == max_met and (best_schedule is None or len(schedule) > len(best_schedule)):
                best_schedule = schedule
                max_met = len(met_friends)
    
    return best_schedule if best_schedule is not None else []

optimal_schedule = find_optimal_schedule()
output = {"itinerary": optimal_schedule}
print(json.dumps(output, indent=2))