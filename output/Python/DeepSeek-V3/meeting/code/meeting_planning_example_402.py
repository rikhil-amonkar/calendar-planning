import json
from itertools import permutations

def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times dictionary: {from_location: {to_location: minutes}}
travel_times = {
    "Golden Gate Park": {
        "Haight-Ashbury": 7,
        "Sunset District": 10,
        "Marina District": 16,
        "Financial District": 26,
        "Union Square": 22
    },
    "Haight-Ashbury": {
        "Golden Gate Park": 7,
        "Sunset District": 15,
        "Marina District": 17,
        "Financial District": 21,
        "Union Square": 17
    },
    "Sunset District": {
        "Golden Gate Park": 11,
        "Haight-Ashbury": 15,
        "Marina District": 21,
        "Financial District": 30,
        "Union Square": 30
    },
    "Marina District": {
        "Golden Gate Park": 18,
        "Haight-Ashbury": 16,
        "Sunset District": 19,
        "Financial District": 17,
        "Union Square": 16
    },
    "Financial District": {
        "Golden Gate Park": 23,
        "Haight-Ashbury": 19,
        "Sunset District": 31,
        "Marina District": 15,
        "Union Square": 9
    },
    "Union Square": {
        "Golden Gate Park": 22,
        "Haight-Ashbury": 18,
        "Sunset District": 26,
        "Marina District": 18,
        "Financial District": 9
    }
}

# Correcting the typo in Marina District key
travel_times["Marina District"] = travel_times.pop("Marina District")

# Friends data: name, location, available_start, available_end, min_duration
friends = [
    ("Sarah", "Haight-Ashbury", "17:00", "21:30", 105),
    ("Patricia", "Sunset District", "17:00", "19:45", 45),
    ("Matthew", "Marina District", "9:15", "12:00", 15),
    ("Joseph", "Financial District", "14:15", "18:45", 30),
    ("Robert", "Union Square", "10:15", "21:45", 15)
]

def calculate_schedule(order):
    current_time = time_to_minutes("9:00")
    current_location = "Golden Gate Park"
    schedule = []
    met_friends = set()
    
    for friend in order:
        name, location, avail_start, avail_end, min_duration = friend
        travel_time = travel_times[current_location][location]
        arrival_time = current_time + travel_time
        avail_start_min = time_to_minutes(avail_start)
        avail_end_min = time_to_minutes(avail_end)
        
        # Calculate possible meeting window
        meeting_start = max(arrival_time, avail_start_min)
        meeting_end = min(meeting_start + min_duration, avail_end_min)
        
        if meeting_end - meeting_start >= min_duration:
            schedule.append({
                "action": "meet",
                "location": location,
                "person": name,
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            })
            met_friends.add(name)
            current_time = meeting_end
            current_location = location
        else:
            # Try to meet at end of their availability
            meeting_end = avail_end_min
            meeting_start = max(avail_start_min, meeting_end - min_duration)
            if meeting_start >= arrival_time and meeting_end - meeting_start >= min_duration:
                schedule.append({
                    "action": "meet",
                    "location": location,
                    "person": name,
                    "start_time": minutes_to_time(meeting_start),
                    "end_time": minutes_to_time(meeting_end)
                })
                met_friends.add(name)
                current_time = meeting_end
                current_location = location
    
    return schedule, len(met_friends)

# Generate all possible orders of meeting friends
all_orders = permutations(friends)

best_schedule = []
max_met = 0

# Try all possible orders to find the best schedule
for order in all_orders:
    schedule, num_met = calculate_schedule(order)
    if num_met > max_met or (num_met == max_met and len(schedule) > len(best_schedule)):
        best_schedule = schedule
        max_met = num_met

# After finding the best schedule, check if we can add more meetings by revisiting
# For simplicity, we'll just return the best found schedule

output = {
    "itinerary": best_schedule
}

print(json.dumps(output, indent=2))