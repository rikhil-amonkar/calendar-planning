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

# Variables for travel times between meetings
travel_vars = {}

# Current time starts at 9:00 AM (540 minutes)
current_time = 540
current_location = "Sunset District"

# We need to model the sequence of meetings
# Let's assume we can meet friends in any order, but must account for travel times

# Create all possible meeting orders
meeting_order = list(friends.keys())
num_meetings = len(meeting_order)

# Variables to track meeting sequence
meeting_sequence = [Int(f"meeting_{i}") for i in range(num_meetings)]
for i in range(num_meetings):
    opt.add(And(meeting_sequence[i] >= 0, meeting_sequence[i] < num_meetings))

# All meetings must be distinct in the sequence
opt.add(Distinct(meeting_sequence))

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
                       meet_vars[name]["start"] >= current_time)))

    # If we don't meet the friend
    opt.add(Implies(Not(meet_vars[name]["met"]), 
                   And(meet_vars[name]["start"] == 0,
                       meet_vars[name]["end"] == 0)))

# Constraints for travel times between meetings
for i in range(num_meetings - 1):
    current_meeting = meeting_sequence[i]
    next_meeting = meeting_sequence[i + 1]
    
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                loc1 = friends[name1]["location"]
                loc2 = friends[name2]["location"]
                travel_time = travel_times[loc1][loc2]
                
                opt.add(Implies(And(meet_vars[name1]["met"],
                                meet_vars[name2]["met"],
                                current_meeting == meeting_order.index(name1),
                                next_meeting == meeting_order.index(name2)),
                       meet_vars[name2]["start"] >= meet_vars[name1]["end"] + travel_time))

# Can't meet Daniel before 9:00 AM
opt.add(Implies(meet_vars["Daniel"]["met"], meet_vars["Daniel"]["start"] >= 540))

# Maximize the number of friends met
opt.maximize(Sum([If(meet_vars[name]["met"], 1, 0) for name in friends]))

# Solve the problem
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    
    # Collect meetings in order
    meeting_order_solution = []
    for i in range(num_meetings):
        meeting_idx = model.evaluate(meeting_sequence[i]).as_long()
        meeting_order_solution.append(meeting_order[meeting_idx])
    
    # Get all meetings that actually happened
    actual_meetings = [name for name in friends if model.evaluate(meet_vars[name]["met"])]
    
    # Sort by actual meeting order
    ordered_meetings = [name for name in meeting_order_solution if name in actual_meetings]
    
    # Build itinerary with proper times
    prev_end = current_time
    prev_loc = current_location
    for name in ordered_meetings:
        start = model.evaluate(meet_vars[name]["start"]).as_long()
        end = model.evaluate(meet_vars[name]["end"]).as_long()
        
        # Add travel time if needed
        if prev_loc != friends[name]["location"]:
            travel_time = travel_times[prev_loc][friends[name]["location"]]
            prev_end += travel_time
        
        itinerary.append({
            "action": "meet",
            "person": name,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end),
        })
        prev_end = end
        prev_loc = friends[name]["location"]
    
    # Output the result
    print({
        "itinerary": itinerary
    })
else:
    print("No feasible schedule found.")