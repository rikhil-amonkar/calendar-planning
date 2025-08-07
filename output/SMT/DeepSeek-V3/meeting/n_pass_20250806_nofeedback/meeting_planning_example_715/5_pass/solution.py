from z3 import *
import json

def solve_scheduling():
    s = Optimize()  # Using Optimize instead of Solver to maximize objectives

    # Define friends and their constraints
    friends = [
        {"name": "Amanda", "location": "Marina District", "available_start": "14:45", "available_end": "19:30", "min_duration": 105},
        {"name": "Melissa", "location": "The Castro", "available_start": "09:30", "available_end": "17:00", "min_duration": 30},
        {"name": "Jeffrey", "location": "Fisherman's Wharf", "available_start": "12:45", "available_end": "18:45", "min_duration": 120},
        {"name": "Matthew", "location": "Bayview", "available_start": "10:15", "available_end": "13:15", "min_duration": 30},
        {"name": "Nancy", "location": "Pacific Heights", "available_start": "17:00", "available_end": "21:30", "min_duration": 105},
        {"name": "Karen", "location": "Mission District", "available_start": "17:30", "available_end": "20:30", "min_duration": 105},
        {"name": "Robert", "location": "Alamo Square", "available_start": "11:15", "available_end": "17:30", "min_duration": 120},
        {"name": "Joseph", "location": "Golden Gate Park", "available_start": "08:30", "available_end": "21:15", "min_duration": 105}
    ]

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Create meeting variables
    for friend in friends:
        available_start = time_to_minutes(friend["available_start"])
        available_end = time_to_minutes(friend["available_end"])
        min_duration = friend["min_duration"]
        
        start = Int(f"{friend['name']}_start")
        end = Int(f"{friend['name']}_end")
        met = Bool(f"met_{friend['name']}")  # Whether we meet this friend
        
        s.add(Implies(met, start >= available_start))
        s.add(Implies(met, end <= available_end))
        s.add(Implies(met, end == start + min_duration))
        
        friend["start_var"] = start
        friend["end_var"] = end
        friend["met_var"] = met

    # Define travel times
    travel_times = {
        ("Presidio", "Marina District"): 11,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Golden Gate Park"): 12,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Golden Gate Park"): 18,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Golden Gate Park"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Mission District"): 22,
        ("Fisherman's Wharf", "Alamo Square"): 21,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Pacific Heights"): 23,
        ("Bayview", "Mission District"): 13,
        ("Bayview", "Alamo Square"): 16,
        ("Bayview", "Golden Gate Park"): 22,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Bayview"): 22,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "Alamo Square"): 10,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Mission District", "Bayview"): 14,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Alamo Square"): 11,
        ("Mission District", "Golden Gate Park"): 17,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Fisherman's Wharf"): 19,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Pacific Heights"): 10,
        ("Alamo Square", "Mission District"): 10,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "Alamo Square"): 9,
    }

    # Sequence variables
    n = len(friends)
    position = [Int(f"pos_{i}") for i in range(n)]
    s.add(Distinct(position))
    for i in range(n):
        s.add(position[i] >= 0, position[i] < n)

    # Initial location and time
    current_time = time_to_minutes("09:00")
    current_location = "Presidio"

    # Constraints for sequence
    for i in range(n):
        for j in range(n):
            if i != j:
                # If friend j comes right after friend i
                s.add(Implies(And(position[i] + 1 == position[j], friends[i]["met_var"], friends[j]["met_var"]),
                      friends[j]["start_var"] >= friends[i]["end_var"] + travel_times.get((friends[i]["location"], friends[j]["location"]), 0))

    # Maximize number of friends met
    s.maximize(Sum([If(friend["met_var"], 1, 0) for friend in friends]))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for friend in friends:
            if is_true(model[friend["met_var"]]):
                start_val = model[friend["start_var"]].as_long()
                end_val = model[friend["end_var"]].as_long()
                itinerary.append({
                    "action": "meet",
                    "person": friend["name"],
                    "start_time": minutes_to_time(start_val),
                    "end_time": minutes_to_time(end_val)
                })
        # Sort by start time
        itinerary.sort(key=lambda x: time_to_minutes(x["start_time"]))
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

result = solve_scheduling()
print(json.dumps(result, indent=2))