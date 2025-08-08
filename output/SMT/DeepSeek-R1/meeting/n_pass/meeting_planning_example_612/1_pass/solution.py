import z3
import json

def main():
    # Define travel_time_dict with all travel times between locations
    travel_time_dict = {
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
        ("Golden Gate Park", "Embarcadero"): 25
    }
    
    # Define friends with their details: (name, location, available_start, available_end, min_time) in minutes from midnight
    friends = [
        ("Emily", "Russian Hill", 12*60+15, 14*60+15, 105),
        ("Mark", "Presidio", 14*60+45, 19*60+30, 60),
        ("Deborah", "Chinatown", 7*60+30, 15*60+30, 45),
        ("Margaret", "Sunset District", 21*60+30, 22*60+30, 60),
        ("George", "The Castro", 7*60+30, 14*60+15, 60),
        ("Andrew", "Embarcadero", 20*60+15, 22*60+0, 75),
        ("Steven", "Golden Gate Park", 11*60+15, 21*60+15, 105)
    ]
    
    # We start at 9:00 AM = 540 minutes from midnight
    start_time_alamo = 540
    
    # Initialize Z3 variables
    num_friends = len(friends)
    included = [z3.Bool(f"included_{i}") for i in range(num_friends)]
    start_vars = [z3.Int(f"start_{i}") for i in range(num_friends)]
    end_vars = [z3.Int(f"end_{i}") for i in range(num_friends)]
    
    # Try from k=7 down to k=1
    k_found = None
    schedule_found = None
    for k in range(num_friends, 0, -1):
        solver = z3.Solver()
        
        # Add constraints for each friend
        for i in range(num_friends):
            # If included, set meeting constraints
            solver.add(z3.Implies(included[i], start_vars[i] >= friends[i][2]))
            solver.add(z3.Implies(included[i], end_vars[i] == start_vars[i] + friends[i][4]))
            solver.add(z3.Implies(included[i], end_vars[i] <= friends[i][3]))
            # Constraint: start time must be at least the travel time from Alamo Square
            loc_i = friends[i][1]
            travel_from_alamo = travel_time_dict[("Alamo Square", loc_i)]
            solver.add(z3.Implies(included[i], start_vars[i] >= start_time_alamo + travel_from_alamo))
        
        # Pairwise disjunctive constraints for meetings
        for i in range(num_friends):
            for j in range(i+1, num_friends):
                loc_i = friends[i][1]
                loc_j = friends[j][1]
                travel_ij = travel_time_dict[(loc_i, loc_j)]
                travel_ji = travel_time_dict[(loc_j, loc_i)]
                # Constraint: if both included, then either i before j or j before i
                constraint_ij = z3.Or(
                    end_vars[i] + travel_ij <= start_vars[j],
                    end_vars[j] + travel_ji <= start_vars[i]
                )
                solver.add(z3.Implies(z3.And(included[i], included[j]), constraint_ij))
        
        # Exactly k meetings included
        solver.add(z3.Sum([z3.If(included[i], 1, 0) for i in range(num_friends)]) == k)
        
        # Check satisfiability
        if solver.check() == z3.sat:
            model = solver.model()
            schedule = []
            for i in range(num_friends):
                if z3.is_true(model[included[i]]):
                    start_val = model.eval(start_vars[i]).as_long()
                    end_val = model.eval(end_vars[i]).as_long()
                    start_hour = start_val // 60
                    start_minute = start_val % 60
                    end_hour = end_val // 60
                    end_minute = end_val % 60
                    schedule.append({
                        "person": friends[i][0],
                        "start_time": f"{start_hour:02d}:{start_minute:02d}",
                        "end_time": f"{end_hour:02d}:{end_minute:02d}"
                    })
            # Sort the schedule by start_time
            schedule.sort(key=lambda x: (int(x['start_time'][:2]), int(x['start_time'][3:5])))
            k_found = k
            schedule_found = schedule
            break
    
    # Prepare the output
    if k_found is None:
        # No schedule found even for k=1? Then empty itinerary
        result = {"itinerary": []}
    else:
        itinerary = [{"action": "meet", "person": item["person"], "start_time": item["start_time"], "end_time": item["end_time"]} for item in schedule_found]
        result = {"itinerary": itinerary}
    
    # Output the solution
    print("SOLUTION:")
    print(json.dumps(result))

if __name__ == "__main__":
    main()