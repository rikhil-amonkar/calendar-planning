from z3 import *

def solve_scheduling():
    s = Solver()

    # Friends data with adjusted time windows to minutes since 9:00 AM
    friends = {
        "Melissa": {"location": "The Castro", "start": 20*60+15-9*60, "end": 21*60+15-9*60, "duration": 30},
        "Kimberly": {"location": "North Beach", "start": 7*60-9*60, "end": 10*60+30-9*60, "duration": 15},
        "Joseph": {"location": "Embarcadero", "start": 15*60+30-9*60, "end": 19*60+30-9*60, "duration": 75},
        "Barbara": {"location": "Alamo Square", "start": 20*60+45-9*60, "end": 21*60+45-9*60, "duration": 15},
        "Kenneth": {"location": "Nob Hill", "start": 12*60+15-9*60, "end": 17*60+15-9*60, "duration": 105},
        "Joshua": {"location": "Presidio", "start": 16*60+30-9*60, "end": 18*60+15-9*60, "duration": 105},
        "Brian": {"location": "Fisherman's Wharf", "start": 9*60+30-9*60, "end": 15*60+30-9*60, "duration": 45},
        "Steven": {"location": "Mission District", "start": 19*60+30-9*60, "end": 21*60-9*60, "duration": 90},
        "Betty": {"location": "Haight-Ashbury", "start": 19*60-9*60, "end": 20*60+30-9*60, "duration": 90}
    }

    # Travel times dictionary
    travel_times = {
        "Union Square": {"The Castro": 17, "North Beach": 10, "Embarcadero": 11, "Alamo Square": 15,
                        "Nob Hill": 9, "Presidio": 24, "Fisherman's Wharf": 15, "Mission District": 14,
                        "Haight-Ashbury": 18},
        "The Castro": {"Union Square": 19, "North Beach": 20, "Embarcadero": 22, "Alamo Square": 8,
                      "Nob Hill": 16, "Presidio": 20, "Fisherman's Wharf": 24, "Mission District": 7,
                      "Haight-Ashbury": 6},
        # ... (rest of travel times remain the same)
    }

    # Create variables
    start_vars = {name: Int(f'start_{name}') for name in friends}
    end_vars = {name: Int(f'end_{name}') for name in friends}
    meet_vars = {name: Bool(f'meet_{name}') for name in friends}  # Whether to meet each friend

    # Basic constraints
    for name in friends:
        data = friends[name]
        s.add(Implies(meet_vars[name], start_vars[name] >= data["start"]))
        s.add(Implies(meet_vars[name], end_vars[name] <= data["end"]))
        s.add(Implies(meet_vars[name], end_vars[name] == start_vars[name] + data["duration"]))

    # Meeting sequence - we'll let Z3 determine the optimal order
    # Create a list of all possible meeting pairs
    meeting_pairs = [(n1, n2) for n1 in friends for n2 in friends if n1 != n2]
    
    # Add constraints for travel times between meetings
    for n1, n2 in meeting_pairs:
        loc1 = friends[n1]["location"]
        loc2 = friends[n2]["location"]
        travel = travel_times[loc1][loc2]
        s.add(Implies(And(meet_vars[n1], meet_vars[n2]),
              Or(end_vars[n1] + travel <= start_vars[n2],
                 end_vars[n2] + travel <= start_vars[n1]))

    # Starting point - must meet at least some friends
    s.add(Or([meet_vars[name] for name in friends]))

    # Optimize to maximize number of meetings
    opt = Optimize()
    for name in friends:
        opt.add_soft(meet_vars[name])
    opt.add(s.assertions())

    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        for name in friends:
            if is_true(m.evaluate(meet_vars[name])):
                start = m.evaluate(start_vars[name]).as_long()
                end = m.evaluate(end_vars[name]).as_long()
                start_time = f"{(start + 9*60)//60:02d}:{(start + 9*60)%60:02d}"
                end_time = f"{(end + 9*60)//60:02d}:{(end + 9*60)%60:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

print(solve_scheduling())