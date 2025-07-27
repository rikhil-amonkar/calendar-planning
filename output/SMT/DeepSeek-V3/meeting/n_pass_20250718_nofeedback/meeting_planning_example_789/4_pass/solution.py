from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver with optimization
    opt = Optimize()

    # Define the friends and their details
    friends = [
        {"name": "Betty", "location": "Russian Hill", "available_start": "07:00", "available_end": "16:45", "min_duration": 105, "priority": 1},
        {"name": "Melissa", "location": "Alamo Square", "available_start": "09:30", "available_end": "17:15", "min_duration": 105, "priority": 1},
        {"name": "Joshua", "location": "Haight-Ashbury", "available_start": "12:15", "available_end": "19:00", "min_duration": 90, "priority": 2},
        {"name": "Jeffrey", "location": "Marina District", "available_start": "12:15", "available_end": "18:00", "min_duration": 45, "priority": 3},
        {"name": "James", "location": "Bayview", "available_start": "07:30", "available_end": "20:00", "min_duration": 90, "priority": 2},
        {"name": "Anthony", "location": "Chinatown", "available_start": "11:45", "available_end": "13:30", "min_duration": 75, "priority": 1},
        {"name": "Timothy", "location": "Presidio", "available_start": "12:30", "available_end": "14:45", "min_duration": 90, "priority": 1},
        {"name": "Emily", "location": "Sunset District", "available_start": "19:30", "available_end": "21:30", "min_duration": 120, "priority": 1}
    ]

    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Define travel times (in minutes)
    travel_times = {
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "Alamo Square"): 15,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Sunset District"): 27,
        ("Russian Hill", "Alamo Square"): 15,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Sunset District"): 23,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Bayview"): 16,
        ("Alamo Square", "Chinatown"): 15,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "Sunset District"): 16,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Sunset District"): 19,
        ("Bayview", "Chinatown"): 19,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Sunset District"): 23,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Sunset District"): 29,
        ("Presidio", "Sunset District"): 16
    }

    # Add symmetric travel times
    for (loc1, loc2), time in list(travel_times.items()):
        if (loc2, loc1) not in travel_times:
            travel_times[(loc2, loc1)] = time

    # Define variables for each meeting
    meetings = {}
    for friend in friends:
        name = friend["name"]
        meetings[name] = {
            "start": Int(f"start_{name}"),
            "end": Int(f"end_{name}"),
            "location": friend["location"],
            "available_start": time_to_minutes(friend["available_start"]),
            "available_end": time_to_minutes(friend["available_end"]),
            "min_duration": friend["min_duration"],
            "priority": friend["priority"],
            "scheduled": Bool(f"scheduled_{name}")
        }

    # Starting at Union Square at 9:00 AM (540 minutes)
    current_time = 540
    current_location = "Union Square"

    # Add constraints for each meeting
    for name, meeting in meetings.items():
        # If scheduled, must be within availability window and meet duration
        opt.add(Implies(meeting["scheduled"],
            And(meeting["start"] >= meeting["available_start"],
                meeting["end"] <= meeting["available_end"],
                meeting["end"] - meeting["start"] >= meeting["min_duration"])))
        
        # If not scheduled, set times to 0
        opt.add(Implies(Not(meeting["scheduled"]),
            And(meeting["start"] == 0, meeting["end"] == 0)))

    # Create ordering variables to sequence meetings
    order = {}
    for i, friend1 in enumerate(friends):
        for j, friend2 in enumerate(friends):
            if i != j:
                name1 = friend1["name"]
                name2 = friend2["name"]
                order[(name1, name2)] = Bool(f"order_{name1}_{name2}")

    # Add ordering constraints
    for (name1, name2), var in order.items():
        loc1 = meetings[name1]["location"]
        loc2 = meetings[name2]["location"]
        travel_time = travel_times.get((loc1, loc2), 0)
        
        opt.add(Implies(And(meetings[name1]["scheduled"], meetings[name2]["scheduled"], var),
            meetings[name1]["end"] + travel_time <= meetings[name2]["start"]))

    # Ensure total ordering
    for i, friend1 in enumerate(friends):
        for j, friend2 in enumerate(friends):
            if i < j:
                name1 = friend1["name"]
                name2 = friend2["name"]
                opt.add(Or(order[(name1, name2)], order[(name2, name1)]))
                opt.add(Not(And(order[(name1, name2)], order[(name2, name1)])))

    # Starting constraints
    for name, meeting in meetings.items():
        travel_time = travel_times.get((current_location, meeting["location"]), 0)
        opt.add(Implies(meetings[name]["scheduled"],
            meetings[name]["start"] >= current_time + travel_time))

    # Maximize the number of scheduled meetings weighted by priority
    total_priority = 0
    for name, meeting in meetings.items():
        total_priority += meeting["priority"] * If(meeting["scheduled"], 1, 0)
    opt.maximize(total_priority)

    # Check for solution
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        
        # Collect scheduled meetings
        scheduled = []
        for name, meeting in meetings.items():
            if is_true(model[meeting["scheduled"]]):
                start = model[meeting["start"]].as_long()
                end = model[meeting["end"]].as_long()
                scheduled.append((start, name))
        
        # Sort by start time
        scheduled.sort()
        
        # Create itinerary
        for start, name in scheduled:
            end = model[meetings[name]["end"]].as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))