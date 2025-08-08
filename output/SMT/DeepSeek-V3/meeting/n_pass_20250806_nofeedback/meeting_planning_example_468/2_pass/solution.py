from z3 import *
import json

# Define the travel times between locations
travel_times = {
    "The Castro": {
        "Bayview": 19,
        "Pacific Heights": 16,
        "Alamo Square": 8,
        "Fisherman's Wharf": 24,
        "Golden Gate Park": 11
    },
    "Bayview": {
        "The Castro": 20,
        "Pacific Heights": 23,
        "Alamo Square": 16,
        "Fisherman's Wharf": 25,
        "Golden Gate Park": 22
    },
    "Pacific Heights": {
        "The Castro": 16,
        "Bayview": 22,
        "Alamo Square": 10,
        "Fisherman's Wharf": 13,
        "Golden Gate Park": 15
    },
    "Alamo Square": {
        "The Castro": 8,
        "Bayview": 16,
        "Pacific Heights": 10,
        "Fisherman's Wharf": 19,
        "Golden Gate Park": 9
    },
    "Fisherman's Wharf": {
        "The Castro": 26,
        "Bayview": 26,
        "Pacific Heights": 12,
        "Alamo Square": 20,
        "Golden Gate Park": 25
    },
    "Golden Gate Park": {
        "The Castro": 13,
        "Bayview": 23,
        "Pacific Heights": 16,
        "Alamo Square": 10,
        "Fisherman's Wharf": 24
    }
}

# Define friends and their availability
friends = {
    "Rebecca": {
        "location": "Bayview",
        "start": 9 * 60,  # 9:00 AM in minutes
        "end": 12 * 60 + 45  # 12:45 PM in minutes
    },
    "Amanda": {
        "location": "Pacific Heights",
        "start": 18 * 60 + 30,  # 6:30 PM in minutes
        "end": 21 * 60 + 45  # 9:45 PM in minutes
    },
    "James": {
        "location": "Alamo Square",
        "start": 9 * 60 + 45,  # 9:45 AM in minutes
        "end": 21 * 60 + 15  # 9:15 PM in minutes
    },
    "Sarah": {
        "location": "Fisherman's Wharf",
        "start": 8 * 60,  # 8:00 AM in minutes
        "end": 21 * 60 + 30  # 9:30 PM in minutes
    },
    "Melissa": {
        "location": "Golden Gate Park",
        "start": 9 * 60,  # 9:00 AM in minutes
        "end": 18 * 60 + 45  # 6:45 PM in minutes
    }
}

# Minimum meeting duration in minutes
min_duration = 90

# Initialize Z3 optimizer
opt = Optimize()

# Create variables for each meeting start and end time
meetings = {}
for friend in friends:
    meetings[friend] = {
        "start": Int(f"start_{friend}"),
        "end": Int(f"end_{friend}"),
        "met": Bool(f"met_{friend}")
    }

# Constraints for each meeting
for friend in friends:
    data = friends[friend]
    start_var = meetings[friend]["start"]
    end_var = meetings[friend]["end"]
    met_var = meetings[friend]["met"]
    
    # If met, then the meeting must be within availability and last at least min_duration
    opt.add(Implies(met_var, start_var >= data["start"]))
    opt.add(Implies(met_var, end_var <= data["end"]))
    opt.add(Implies(met_var, end_var == start_var + min_duration))
    
    # If not met, then the meeting times are unconstrained
    opt.add(Implies(Not(met_var), start_var == 0))
    opt.add(Implies(Not(met_var), end_var == 0))

# Maximize the number of friends met
opt.maximize(Sum([If(meetings[friend]["met"], 1, 0) for friend in friends]))

# Check if the optimizer can find a solution
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    
    # Collect all meetings that are scheduled
    for friend in friends:
        if model.evaluate(meetings[friend]["met"]):
            start = model.evaluate(meetings[friend]["start"]).as_long()
            end = model.evaluate(meetings[friend]["end"]).as_long()
            
            # Convert minutes to HH:MM format
            start_hh = start // 60
            start_mm = start % 60
            end_hh = end // 60
            end_mm = end % 60
            
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": f"{start_hh:02d}:{start_mm:02d}",
                "end_time": f"{end_hh:02d}:{end_mm:02d}"
            })
    
    # Sort itinerary by start time
    itinerary.sort(key=lambda x: x["start_time"])
    
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print('No solution found')