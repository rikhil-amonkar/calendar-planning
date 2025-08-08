from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver with optimization capabilities
    opt = Optimize()

    # Define friends and their availability
    friends = {
        "Emily": {"location": "Russian Hill", "start": "12:15", "end": "14:15", "min_duration": 105},
        "Mark": {"location": "Presidio", "start": "14:45", "end": "19:30", "min_duration": 60},
        "Deborah": {"location": "Chinatown", "start": "07:30", "end": "15:30", "min_duration": 45},
        "Margaret": {"location": "Sunset District", "start": "21:30", "end": "22:30", "min_duration": 60},
        "George": {"location": "The Castro", "start": "07:30", "end": "14:15", "min_duration": 60},
        "Andrew": {"location": "Embarcadero", "start": "20:15", "end": "22:00", "min_duration": 75},
        "Steven": {"location": "Golden Gate Park", "start": "11:15", "end": "21:15", "min_duration": 105}
    }

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Initialize variables for each meeting
    meeting_vars = {}
    for name in friends:
        start_var = Int(f"start_{name}")
        end_var = Int(f"end_{name}")
        meeting_vars[name] = {"start": start_var, "end": end_var}

    # Add basic meeting constraints
    for name, info in friends.items():
        start_time = time_to_minutes(info["start"])
        end_time = time_to_minutes(info["end"])
        min_duration = info["min_duration"]

        opt.add(meeting_vars[name]["start"] >= start_time)
        opt.add(meeting_vars[name]["end"] <= end_time)
        opt.add(meeting_vars[name]["end"] - meeting_vars[name]["start"] >= min_duration)

    # Define travel times
    travel_times = {
        ("Alamo Square", "Russian Hill"): 13,
        ("Alamo Square", "Presidio"): 18,
        ("Alamo Square", "Chinatown"): 16,
        ("Alamo Square", "Sunset District"): 16,
        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Embarcadero"): 17,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("Presidio", "Alamo Square"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Sunset District"): 15,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Golden Gate Park"): 12,
        ("Chinatown", "Alamo Square"): 17,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Sunset District"): 29,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Chinatown"): 30,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Embarcadero"): 31,
        ("Sunset District", "Golden Gate Park"): 11,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Chinatown"): 20,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Golden Gate Park"): 11,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Sunset District"): 30,
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Golden Gate Park", "Alamo Square"): 10,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Embarcadero"): 25,
    }

    # Define meeting order variables
    order = [Int(f"order_{name}") for name in friends]
    opt.add(Distinct(order))
    for o in order:
        opt.add(o >= 0, o < len(friends))

    # Starting point
    current_location = "Alamo Square"
    current_time = time_to_minutes("09:00")  # 9:00 AM

    # Add travel time constraints between meetings
    for i in range(len(friends)):
        for j in range(len(friends)):
            if i != j:
                name_i = list(friends.keys())[i]
                name_j = list(friends.keys())[j]
                loc_i = friends[name_i]["location"]
                loc_j = friends[name_j]["location"]
                
                # If meeting i comes before meeting j
                opt.add(Implies(
                    order[i] < order[j],
                    meeting_vars[name_j]["start"] >= meeting_vars[name_i]["end"] + travel_times[(loc_i, loc_j)]
                ))

    # First meeting must be reachable from starting point
    for name in friends:
        loc = friends[name]["location"]
        opt.add(Implies(
            order[list(friends.keys()).index(name)] == 0,
            meeting_vars[name]["start"] >= current_time + travel_times[(current_location, loc)]
        ))

    # Create a variable to count met friends
    met_friends = [Bool(f"met_{name}") for name in friends]
    for i, name in enumerate(friends):
        opt.add(met_friends[i] == (meeting_vars[name]["end"] > meeting_vars[name]["start"]))

    # Maximize the number of friends met
    opt.maximize(Sum([If(m, 1, 0) for m in met_friends]))

    # Check for solution
    if opt.check() == sat:
        model = opt.model()
        # Get the meeting order
        meeting_order = sorted(
            [(name, model[order[i]].as_long()) for i, name in enumerate(friends)],
            key=lambda x: x[1]
        )
        itinerary = []
        for name, _ in meeting_order:
            start = model[meeting_vars[name]["start"]].as_long()
            end = model[meeting_vars[name]["end"]].as_long()
            if start < end:  # Only include actual meetings
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": minutes_to_time(start),
                    "end_time": minutes_to_time(end)
                })
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve the scheduling problem
result = solve_scheduling()

# Print the result in JSON format
print(json.dumps(result, indent=2))