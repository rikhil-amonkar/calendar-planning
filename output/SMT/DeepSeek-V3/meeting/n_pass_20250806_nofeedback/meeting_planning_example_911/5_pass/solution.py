from z3 import *
import json

def solve_scheduling():
    s = Optimize()

    # Friends data with time in hours (9:00AM = 9.0)
    friends = {
        "Steven": {"location": "North Beach", "start": 17.5, "end": 20.5, "duration": 0.25},
        "Sarah": {"location": "Golden Gate Park", "start": 17.0, "end": 19.25, "duration": 1.25},
        "Brian": {"location": "Embarcadero", "start": 14.25, "end": 16.0, "duration": 1.75},
        "Stephanie": {"location": "Haight-Ashbury", "start": 10.25, "end": 12.25, "duration": 1.25},
        "Melissa": {"location": "Richmond District", "start": 14.0, "end": 19.5, "duration": 0.5},
        "Nancy": {"location": "Nob Hill", "start": 8.25, "end": 12.75, "duration": 1.5},
        "David": {"location": "Marina District", "start": 11.25, "end": 13.25, "duration": 2.0},
        "James": {"location": "Presidio", "start": 15.0, "end": 18.25, "duration": 2.0},
        "Elizabeth": {"location": "Union Square", "start": 11.5, "end": 21.0, "duration": 1.0},
        "Robert": {"location": "Financial District", "start": 13.25, "end": 15.25, "duration": 0.75}
    }

    # Travel times in hours (convert from minutes)
    travel_times = {
        ("The Castro", "North Beach"): 20/60,
        ("The Castro", "Golden Gate Park"): 11/60,
        ("The Castro", "Embarcadero"): 22/60,
        ("The Castro", "Haight-Ashbury"): 6/60,
        ("The Castro", "Richmond District"): 16/60,
        ("The Castro", "Nob Hill"): 16/60,
        ("The Castro", "Marina District"): 21/60,
        ("The Castro", "Presidio"): 20/60,
        ("The Castro", "Union Square"): 19/60,
        ("The Castro", "Financial District"): 21/60,
        ("North Beach", "Golden Gate Park"): 22/60,
        ("North Beach", "Embarcadero"): 6/60,
        ("North Beach", "Haight-Ashbury"): 18/60,
        ("North Beach", "Richmond District"): 18/60,
        ("North Beach", "Nob Hill"): 7/60,
        ("North Beach", "Marina District"): 9/60,
        ("North Beach", "Presidio"): 17/60,
        ("North Beach", "Union Square"): 7/60,
        ("North Beach", "Financial District"): 8/60,
        ("Golden Gate Park", "Embarcadero"): 25/60,
        ("Golden Gate Park", "Haight-Ashbury"): 7/60,
        ("Golden Gate Park", "Richmond District"): 7/60,
        ("Golden Gate Park", "Nob Hill"): 20/60,
        ("Golden Gate Park", "Marina District"): 16/60,
        ("Golden Gate Park", "Presidio"): 11/60,
        ("Golden Gate Park", "Union Square"): 22/60,
        ("Golden Gate Park", "Financial District"): 26/60,
        ("Embarcadero", "Haight-Ashbury"): 21/60,
        ("Embarcadero", "Richmond District"): 21/60,
        ("Embarcadero", "Nob Hill"): 10/60,
        ("Embarcadero", "Marina District"): 12/60,
        ("Embarcadero", "Presidio"): 20/60,
        ("Embarcadero", "Union Square"): 10/60,
        ("Embarcadero", "Financial District"): 5/60,
        ("Haight-Ashbury", "Richmond District"): 10/60,
        ("Haight-Ashbury", "Nob Hill"): 15/60,
        ("Haight-Ashbury", "Marina District"): 17/60,
        ("Haight-Ashbury", "Presidio"): 15/60,
        ("Haight-Ashbury", "Union Square"): 19/60,
        ("Haight-Ashbury", "Financial District"): 21/60,
        ("Richmond District", "Nob Hill"): 17/60,
        ("Richmond District", "Marina District"): 9/60,
        ("Richmond District", "Presidio"): 7/60,
        ("Richmond District", "Union Square"): 21/60,
        ("Richmond District", "Financial District"): 22/60,
        ("Nob Hill", "Marina District"): 11/60,
        ("Nob Hill", "Presidio"): 17/60,
        ("Nob Hill", "Union Square"): 7/60,
        ("Nob Hill", "Financial District"): 9/60,
        ("Marina District", "Presidio"): 10/60,
        ("Marina District", "Union Square"): 16/60,
        ("Marina District", "Financial District"): 17/60,
        ("Presidio", "Union Square"): 22/60,
        ("Presidio", "Financial District"): 23/60,
        ("Union Square", "Financial District"): 9/60
    }

    # Create variables for each meeting
    meeting_vars = {}
    for name in friends:
        start = Real(f"{name}_start")
        end = Real(f"{name}_end")
        meeting_vars[name] = {"start": start, "end": end}

    # Add basic constraints for each meeting
    for name in friends:
        friend = friends[name]
        s.add(meeting_vars[name]["start"] >= friend["start"])
        s.add(meeting_vars[name]["end"] <= friend["end"])
        s.add(meeting_vars[name]["end"] == meeting_vars[name]["start"] + friend["duration"])

    # Create variables for meeting order
    order = {name: Int(f"order_{name}") for name in friends}
    s.add(Distinct([order[name] for name in friends]))
    for name in friends:
        s.add(order[name] >= 0, order[name] < len(friends))

    # Starting point is The Castro at 9:00AM
    # Only Nancy can start at 9:00AM (earliest available meeting)
    s.add(order["Nancy"] == 0)
    s.add(meeting_vars["Nancy"]["start"] == 9.0)

    # Add travel time constraints between consecutive meetings
    for i in range(len(friends)-1):
        for name1 in friends:
            for name2 in friends:
                if name1 != name2:
                    # If name1 comes right before name2 in order
                    before = And(order[name1] == i, order[name2] == i+1)
                    loc1 = friends[name1]["location"]
                    loc2 = friends[name2]["location"]
                    
                    # Get travel time (default to 30 minutes if not found)
                    travel_time = travel_times.get((loc1, loc2), 0.5)
                    
                    # Add constraint that name2 starts after name1 ends + travel time
                    s.add(Implies(before, 
                                 meeting_vars[name2]["start"] >= meeting_vars[name1]["end"] + travel_time))

    # Helper function to convert Z3 values to time strings
    def z3_to_time(val):
        if is_rational_value(val):
            f = float(val.as_fraction())
        else:
            f = float(str(val))
        hours = int(f)
        minutes = int((f - hours) * 60)
        return f"{hours:02d}:{minutes:02d}"

    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in friends:
            start_time = z3_to_time(m[meeting_vars[name]["start"]])
            end_time = z3_to_time(m[meeting_vars[name]["end"]])
            itinerary.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
        
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        return {"itinerary": itinerary}
    else:
        # Try relaxing constraints if no solution found
        # First, try reducing meeting durations by 15 minutes
        for name in friends:
            friends[name]["duration"] = max(0, friends[name]["duration"] - 0.25)
            s.add(meeting_vars[name]["end"] == meeting_vars[name]["start"] + friends[name]["duration"])
        
        if s.check() == sat:
            m = s.model()
            itinerary = []
            for name in friends:
                start_time = z3_to_time(m[meeting_vars[name]["start"]])
                end_time = z3_to_time(m[meeting_vars[name]["end"]])
                itinerary.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
            
            itinerary.sort(key=lambda x: x["start_time"])
            return {"itinerary": itinerary, "note": "Some meeting durations were reduced to find a feasible schedule"}
        else:
            return {"error": "No valid schedule found even after relaxing constraints"}

solution = solve_scheduling()
print("SOLUTION:")
print(json.dumps(solution, indent=2))