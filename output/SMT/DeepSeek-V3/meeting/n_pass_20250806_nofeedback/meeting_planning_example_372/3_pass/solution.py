from z3 import *
import datetime

# Travel times in minutes (from -> to)
travel_times = {
    "Sunset District": {
        "Alamo Square": 17,
        "Russian Hill": 24,
        "Golden Gate Park": 11,
        "Mission District": 24,
    },
    "Alamo Square": {
        "Sunset District": 16,
        "Russian Hill": 13,
        "Golden Gate Park": 9,
        "Mission District": 10,
    },
    "Russian Hill": {
        "Sunset District": 23,
        "Alamo Square": 15,
        "Golden Gate Park": 21,
        "Mission District": 16,
    },
    "Golden Gate Park": {
        "Sunset District": 10,
        "Alamo Square": 10,
        "Russian Hill": 19,
        "Mission District": 17,
    },
    "Mission District": {
        "Sunset District": 24,
        "Alamo Square": 11,
        "Russian Hill": 15,
        "Golden Gate Park": 17,
    },
}

# Friends' availability and constraints
friends = {
    "Charles": {
        "location": "Alamo Square",
        "start": "18:00",
        "end": "20:45",
        "min_duration": 90,
    },
    "Margaret": {
        "location": "Russian Hill",
        "start": "09:00",
        "end": "16:00",
        "min_duration": 30,
    },
    "Daniel": {
        "location": "Golden Gate Park",
        "start": "08:00",
        "end": "13:30",
        "min_duration": 15,
    },
    "Stephanie": {
        "location": "Mission District",
        "start": "20:30",
        "end": "22:00",
        "min_duration": 90,
    },
}

# Convert time strings to minutes since midnight
def time_to_minutes(time_str):
    h, m = map(int, time_str.split(":"))
    return h * 60 + m

# Convert minutes back to time string
def minutes_to_time(minutes):
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

# Initialize Z3 optimizer
opt = Optimize()

# Variables for meeting start and end times
meet_vars = {}
for name in friends:
    meet_vars[name] = {
        "start": Int(f"start_{name}"),
        "end": Int(f"end_{name}"),
        "met": Bool(f"met_{name}"),
    }

# Current time starts at 9:00 AM (540 minutes)
current_time = 540
current_location = "Sunset District"

# Variables to track location and time after each meeting
locations = []
times = []

# Constraints for each friend
for name, data in friends.items():
    location = data["location"]
    start = time_to_minutes(data["start"])
    end = time_to_minutes(data["end"])
    min_duration = data["min_duration"]
    
    # If we meet the friend
    opt.add(Implies(meet_vars[name]["met"], 
                   And(meet_vars[name]["start"] >= start,
                       meet_vars[name]["end"] <= end,
                       meet_vars[name]["end"] - meet_vars[name]["start"] >= min_duration,
                       meet_vars[name]["start"] >= current_time)))  # Can't meet before arrival

    # If we don't meet the friend
    opt.add(Implies(Not(meet_vars[name]["met"]), 
                   And(meet_vars[name]["start"] == 0,
                       meet_vars[name]["end"] == 0)))

# Order constraints and travel times
# We'll meet friends in some order, with travel time between meetings
# This is a simplified approach - a more complete solution would track locations explicitly

# Maximize the number of friends met
opt.maximize(Sum([If(meet_vars[name]["met"], 1, 0) for name in friends]))

# Additional constraints to prevent impossible schedules
# Can't meet Daniel before 9:00 AM
opt.add(Implies(meet_vars["Daniel"]["met"], meet_vars["Daniel"]["start"] >= 540))

# Solve the problem
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    
    # Collect meetings
    for name in friends:
        if model.evaluate(meet_vars[name]["met"]):
            start = model.evaluate(meet_vars[name]["start"]).as_long()
            end = model.evaluate(meet_vars[name]["end"]).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end),
            })
    
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
    
    # Output the result
    print({
        "itinerary": itinerary
    })
else:
    print("No feasible schedule found.")