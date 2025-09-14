import json
from z3 import Optimize, If, Int, Bool, And, Or, Implies, sat

def format_time(t):
    # Convert minutes since midnight to a string in H:MM format.
    hours = t // 60
    minutes = t % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Our day starts at 9:00 (540 minutes) at "The Castro"
    arrival_time = 9 * 60
    start_location = "The Castro"

    # Define the meeting information for each friend.
    # Times are in minutes from midnight.
    persons = [
        {"name": "Steven",    "location": "North Beach",        "avail_start": 17*60+30, "avail_end": 20*60+30, "min_duration": 15},
        {"name": "Sarah",     "location": "Golden Gate Park",   "avail_start": 17*60,    "avail_end": 19*60+15, "min_duration": 75},
        {"name": "Brian",     "location": "Embarcadero",        "avail_start": 14*60+15, "avail_end": 16*60,    "min_duration": 105},
        {"name": "Stephanie", "location": "Haight-Ashbury",     "avail_start": 10*60+15, "avail_end": 12*60+15, "min_duration": 75},
        {"name": "Melissa",   "location": "Richmond District",  "avail_start": 14*60,    "avail_end": 19*60+30, "min_duration": 30},
        {"name": "Nancy",     "location": "Nob Hill",           "avail_start": 8*60+15,  "avail_end": 12*60+45, "min_duration": 90},
        {"name": "David",     "location": "Marina District",    "avail_start": 11*60+15, "avail_end": 13*60+15, "min_duration": 120},
        {"name": "James",     "location": "Presidio",           "avail_start": 15*60,    "avail_end": 18*60+15, "min_duration": 120},
        {"name": "Elizabeth", "location": "Union Square",       "avail_start": 11*60+30, "avail_end": 21*60,    "min_duration": 60},
        {"name": "Robert",    "location": "Financial District", "avail_start": 13*60+15, "avail_end": 15*60+15, "min_duration": 45},
    ]

    # Define the travel times (in minutes) between locations.
    travel_times = {
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Financial District"): 21,
        
        ("North Beach", "The Castro"): 23,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Financial District"): 8,
        
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Financial District"): 26,
        
        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Financial District"): 5,
        
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Financial District"): 21,
        
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Financial District"): 22,
        
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Financial District"): 9,
        
        ("Marina District", "The Castro"): 22,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Financial District"): 17,
        
        ("Presidio", "The Castro"): 21,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Financial District"): 23,
        
        ("Union Square", "The Castro"): 17,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Financial District"): 9,
        
        ("Financial District", "The Castro"): 20,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Union Square"): 9
    }

    # Create an Optimize instance and variables for each meeting
    opt = Optimize()
    x_vars = {}     # Boolean variables indicating whether to schedule a meeting
    start_vars = {} # Integer variables representing the start time of the meeting

    for p in persons:
        pname = p["name"].replace(" ", "_")
        x_vars[pname] = Bool("x_" + pname)
        start_vars[pname] = Int("start_" + pname)
        # If scheduled, the meeting must begin within the person's available window.
        opt.add(Implies(x_vars[pname], start_vars[pname] >= p["avail_start"]))
        opt.add(Implies(x_vars[pname], start_vars[pname] + p["min_duration"] <= p["avail_end"]))
        # The meeting must start after arriving from the initial location ("The Castro")
        opt.add(Implies(x_vars[pname], start_vars[pname] >= arrival_time + travel_times[(start_location, p["location"])]))

    # For any two meetings, if both are scheduled, then they cannot overlap once travel times are taken into account.
    for i in range(len(persons)):
        for j in range(i+1, len(persons)):
            p = persons[i]
            q = persons[j]
            pname = p["name"].replace(" ", "_")
            qname = q["name"].replace(" ", "_")
            travel_pq = travel_times[(p["location"], q["location"])]
            travel_qp = travel_times[(q["location"], p["location"])]
            opt.add(Implies(And(x_vars[pname], x_vars[qname]),
                Or(
                    start_vars[pname] + p["min_duration"] + travel_pq <= start_vars[qname],
                    start_vars[qname] + q["min_duration"] + travel_qp <= start_vars[pname]
                )
            ))

    # Objective: maximize the total number of meetings scheduled.
    objective = sum([If(x_vars[p["name"].replace(" ", "_")], 1, 0) for p in persons])
    opt.maximize(objective)

    if opt.check() == sat:
        model = opt.model()
        scheduled_meetings = []
        for p in persons:
            pname = p["name"].replace(" ", "_")
            if model.evaluate(x_vars[pname]):
                start_time_model = model.evaluate(start_vars[pname]).as_long()
                end_time_model = start_time_model + p["min_duration"]
                scheduled_meetings.append({
                    "action": "meet",
                    "location": p["location"],
                    "person": p["name"],
                    "start_time": format_time(start_time_model),
                    "end_time": format_time(end_time_model)
                })
        # Sort the meetings in chronological order using the computed start times.
        scheduled_meetings.sort(key=lambda m: int(m["start_time"].split(":")[0]) * 60 + int(m["start_time"].split(":")[1]))
        result = {"itinerary": scheduled_meetings}
        print(json.dumps(result, indent=2))
    else:
        # If the constraints are unsatisfiable, output an empty itinerary.
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()