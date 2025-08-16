from z3 import *

# Helper function to convert minutes since midnight (integer) to HH:MM format
def minutes_to_time(m):
    h = m // 60
    minute = m % 60
    return f"{h:02d}:{minute:02d}"

def main():
    # Define friend meeting data.
    # Times are in minutes since midnight.
    # For example: 9:00AM = 540, 13:15 = 795, etc.
    friends = [
      {"name": "Elizabeth", "loc": "Marina District", "start": 1140, "end": 1245, "min": 105},
      {"name": "Joshua",    "loc": "Presidio",        "start": 510,  "end": 795,  "min": 105},
      {"name": "Timothy",   "loc": "North Beach",     "start": 1185, "end": 1320, "min": 90},
      {"name": "David",     "loc": "Embarcadero",     "start": 645,  "end": 750,  "min": 30},
      {"name": "Kimberly",  "loc": "Haight-Ashbury",  "start": 1005, "end": 1290, "min": 75},
      {"name": "Lisa",      "loc": "Golden Gate Park", "start": 1050, "end": 1305, "min": 45},
      {"name": "Ronald",    "loc": "Richmond District", "start": 480, "end": 570,  "min": 90},
      {"name": "Stephanie", "loc": "Alamo Square",    "start": 930,  "end": 990,  "min": 30},
      {"name": "Helen",     "loc": "Financial District", "start": 1050, "end": 1110, "min": 45},
      {"name": "Laura",     "loc": "Sunset District", "start": 1065, "end": 1275, "min": 90},
    ]
    num_friends = len(friends)
    
    # Travel times (in minutes) between locations.
    # These are directional (so "A"->"B" can differ from "B"->"A").
    travel = {
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Alamo Square"): 8,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Sunset District"): 17,

        ("Marina District", "The Castro"): 22,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Alamo Square"): 15,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Sunset District"): 19,

        ("Presidio", "The Castro"): 21,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Alamo Square"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Sunset District"): 15,

        ("North Beach", "The Castro"): 23,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Alamo Square"): 16,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Sunset District"): 27,

        ("Embarcadero", "The Castro"): 25,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Alamo Square"): 19,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Sunset District"): 30,

        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Golden Gate Park"): 7,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Alamo Square"): 5,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Sunset District"): 15,

        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Alamo Square"): 9,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "Sunset District"): 10,

        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Alamo Square"): 13,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Sunset District"): 11,

        ("Alamo Square", "The Castro"): 8,
        ("Alamo Square", "Marina District"): 15,
        ("Alamo Square", "Presidio"): 17,
        ("Alamo Square", "North Beach"): 15,
        ("Alamo Square", "Embarcadero"): 16,
        ("Alamo Square", "Haight-Ashbury"): 5,
        ("Alamo Square", "Golden Gate Park"): 9,
        ("Alamo Square", "Richmond District"): 11,
        ("Alamo Square", "Financial District"): 17,
        ("Alamo Square", "Sunset District"): 16,

        ("Financial District", "The Castro"): 20,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Alamo Square"): 17,
        ("Financial District", "Sunset District"): 30,

        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "North Beach"): 28,
        ("Sunset District", "Embarcadero"): 30,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Alamo Square"): 17,
        ("Sunset District", "Financial District"): 30,
    }
    
    # Helper function to fetch travel times.
    def get_travel_time(origin, dest):
        # Default to a very large number if not defined.
        return travel.get((origin, dest), 9999)
    
    # Create an Optimize instance.
    opt = Optimize()
    
    # Decision variables for each friend:
    # s_vars[i]: meeting start time
    # e_vars[i]: meeting end time
    # order_vars[i]: the position in the schedule (if meeting is scheduled, an integer 1..num_friends; else 0)
    # sel_vars[i]: Boolean; True if meeting is scheduled.
    s_vars = [Int(f"s_{i}") for i in range(num_friends)]
    e_vars = [Int(f"e_{i}") for i in range(num_friends)]
    order_vars = [Int(f"order_{i}") for i in range(num_friends)]
    sel_vars = [Bool(f"sel_{i}") for i in range(num_friends)]
    
    # For each friend meeting, add the availability and duration constraints.
    for i, f in enumerate(friends):
        start_avail = f["start"]
        end_avail = f["end"]
        min_dur = f["min"]
        # If meeting is selected, its start must be no earlier than available start 
        # and its end no later than available end; also the meeting must last at least min_dur.
        opt.add(Implies(sel_vars[i], s_vars[i] >= start_avail))
        opt.add(Implies(sel_vars[i], e_vars[i] <= end_avail))
        opt.add(Implies(sel_vars[i], e_vars[i] - s_vars[i] >= min_dur))
        # If not selected, fix times (they won’t be used).
        opt.add(Implies(Not(sel_vars[i]), s_vars[i] == 0))
        opt.add(Implies(Not(sel_vars[i]), e_vars[i] == 0))
        # Order variable: if selected then must be in range 1 ... num_friends; otherwise 0.
        opt.add(Implies(sel_vars[i], And(order_vars[i] >= 1, order_vars[i] <= num_friends)))
        opt.add(Implies(Not(sel_vars[i]), order_vars[i] == 0))
    
    # Ensure that any two selected meetings get distinct order numbers.
    for i in range(num_friends):
        for j in range(i+1, num_friends):
            opt.add(Implies(And(sel_vars[i], sel_vars[j]), order_vars[i] != order_vars[j]))
    
    # Travel time constraints for consecutive meetings.
    # For any two meetings i and j, if both are selected and meeting j is scheduled immediately after meeting i 
    # (i.e. order[j] == order[i]+1), then meeting j cannot start until meeting i is finished plus the travel time from i's location to j's.
    for i in range(num_friends):
        for j in range(num_friends):
            if i != j:
                travel_ij = get_travel_time(friends[i]["loc"], friends[j]["loc"])
                opt.add(Implies(And(sel_vars[i], sel_vars[j], order_vars[j] == order_vars[i] + 1),
                                s_vars[j] >= e_vars[i] + travel_ij))
    
    # Constraint for the first meeting:
    # You start at The Castro at 9:00 (540 minutes). Thus the meeting that is first in the ordering must 
    # not start before you can reach it.
    for i in range(num_friends):
        travel_from_castro = get_travel_time("The Castro", friends[i]["loc"])
        opt.add(Implies(And(sel_vars[i], order_vars[i] == 1),
                        s_vars[i] >= 540 + travel_from_castro))
    
    # Objective: maximize the number of meetings scheduled.
    opt.maximize(Sum([If(sel, 1, 0) for sel in sel_vars]))
    
    if opt.check() == sat:
        model = opt.model()
        scheduled = []
        for i in range(num_friends):
            if is_true(model.evaluate(sel_vars[i])):
                order_val = model.evaluate(order_vars[i]).as_long()
                s_val = model.evaluate(s_vars[i]).as_long()
                e_val = model.evaluate(e_vars[i]).as_long()
                scheduled.append((order_val, friends[i]["name"], s_val, e_val))
        # Sort the scheduled meetings in order.
        scheduled.sort(key=lambda x: x[0])
        
        itinerary = []
        for order_val, name, s_val, e_val in scheduled:
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(s_val),
                "end_time": minutes_to_time(e_val)
            })
        # Output the result in JSON format.
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()