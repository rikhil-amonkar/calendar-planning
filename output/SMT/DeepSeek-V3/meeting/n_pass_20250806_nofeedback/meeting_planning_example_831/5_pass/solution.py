from z3 import *
import json

def solve_scheduling():
    # Initialize Z3 solver
    s = Optimize()

    # Friends and their details (times in minutes since midnight)
    friends = {
        "Jeffrey": {"location": "Fisherman's Wharf", "start": 615, "end": 780, "min_duration": 90},
        "Ronald": {"location": "Alamo Square", "start": 465, "end": 885, "min_duration": 120},
        "Jason": {"location": "Financial District", "start": 645, "end": 960, "min_duration": 105},
        "Melissa": {"location": "Union Square", "start": 1065, "end": 1095, "min_duration": 15},
        "Elizabeth": {"location": "Sunset District", "start": 885, "end": 1050, "min_duration": 105},
        "Margaret": {"location": "Embarcadero", "start": 795, "end": 1140, "min_duration": 90},
        "George": {"location": "Golden Gate Park", "start": 1140, "end": 1260, "min_duration": 75},
        "Richard": {"location": "Chinatown", "start": 570, "end": 1260, "min_duration": 15},
        "Laura": {"location": "Richmond District", "start": 585, "end": 1080, "min_duration": 60}
    }

    # Travel times between locations (in minutes)
    travel_times = {
        "Presidio": {
            "Fisherman's Wharf": 19, "Alamo Square": 19, "Financial District": 23,
            "Union Square": 22, "Sunset District": 15, "Embarcadero": 20,
            "Golden Gate Park": 12, "Chinatown": 21, "Richmond District": 7
        },
        "Fisherman's Wharf": {
            "Presidio": 17, "Alamo Square": 21, "Financial District": 11,
            "Union Square": 13, "Sunset District": 27, "Embarcadero": 8,
            "Golden Gate Park": 25, "Chinatown": 12, "Richmond District": 18
        },
        "Alamo Square": {
            "Presidio": 17, "Fisherman's Wharf": 19, "Financial District": 17,
            "Union Square": 14, "Sunset District": 16, "Embarcadero": 16,
            "Golden Gate Park": 9, "Chinatown": 15, "Richmond District": 11
        },
        "Financial District": {
            "Presidio": 22, "Fisherman's Wharf": 10, "Alamo Square": 17,
            "Union Square": 9, "Sunset District": 30, "Embarcadero": 4,
            "Golden Gate Park": 23, "Chinatown": 5, "Richmond District": 21
        },
        "Union Square": {
            "Presidio": 24, "Fisherman's Wharf": 15, "Alamo Square": 15,
            "Financial District": 9, "Sunset District": 27, "Embarcadero": 11,
            "Golden Gate Park": 22, "Chinatown": 7, "Richmond District": 20
        },
        "Sunset District": {
            "Presidio": 16, "Fisherman's Wharf": 29, "Alamo Square": 17,
            "Financial District": 30, "Union Square": 30, "Embarcadero": 30,
            "Golden Gate Park": 11, "Chinatown": 30, "Richmond District": 12
        },
        "Embarcadero": {
            "Presidio": 20, "Fisherman's Wharf": 6, "Alamo Square": 19,
            "Financial District": 5, "Union Square": 10, "Sunset District": 30,
            "Golden Gate Park": 25, "Chinatown": 7, "Richmond District": 21
        },
        "Golden Gate Park": {
            "Presidio": 11, "Fisherman's Wharf": 24, "Alamo Square": 9,
            "Financial District": 26, "Union Square": 22, "Sunset District": 10,
            "Embarcadero": 25, "Chinatown": 23, "Richmond District": 7
        },
        "Chinatown": {
            "Presidio": 19, "Fisherman's Wharf": 8, "Alamo Square": 17,
            "Financial District": 5, "Union Square": 7, "Sunset District": 29,
            "Embarcadero": 5, "Golden Gate Park": 23, "Richmond District": 20
        },
        "Richmond District": {
            "Presidio": 7, "Fisherman's Wharf": 18, "Alamo Square": 13,
            "Financial District": 22, "Union Square": 21, "Sunset District": 11,
            "Embarcadero": 19, "Golden Gate Park": 9, "Chinatown": 20
        }
    }

    # Variables
    start_times = {name: Int(f"start_{name}") for name in friends}
    scheduled = {name: Bool(f"sched_{name}") for name in friends}
    current_location = "Presidio"
    current_time = 540  # 9:00 AM in minutes

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        s.add(Implies(scheduled[name],
                     And(start_times[name] >= friend["start"],
                         start_times[name] + friend["min_duration"] <= friend["end"])))

    # Determine meeting order
    order = [Int(f"order_{i}") for i in range(len(friends))]
    s.add(Distinct(order))
    for o in order:
        s.add(o >= 0)
        s.add(o < len(friends))

    # Link order to actual meetings
    prev_end = current_time
    prev_loc = current_location
    for i in range(len(friends)):
        # For each position in order, determine which meeting happens there
        for j, name in enumerate(friends):
            s.add(Implies(And(order[i] == j, scheduled[name]),
                         And(start_times[name] >= prev_end + travel_times[prev_loc][friends[name]["location"]],
                             prev_end == start_times[name] + friends[name]["min_duration"],
                             prev_loc == friends[name]["location"])))

    # Maximize number of scheduled meetings
    s.maximize(Sum([If(scheduled[name], 1, 0) for name in friends]))

    if s.check() == sat:
        model = s.model()
        itinerary = []
        
        # Get the meeting order
        meeting_order = sorted([(model.evaluate(order[i]).as_long(), i) 
                              for i in range(len(friends))], key=lambda x: x[0])
        
        for pos, i in meeting_order:
            name = list(friends.keys())[i]
            if model.evaluate(scheduled[name]):
                start = model.evaluate(start_times[name]).as_long()
                end = start + friends[name]["min_duration"]
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": f"{start//60:02d}:{start%60:02d}",
                    "end_time": f"{end//60:02d}:{end%60:02d}"
                })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

solution = solve_scheduling()
print(json.dumps(solution, indent=2))