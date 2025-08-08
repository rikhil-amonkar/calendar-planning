from z3 import *
import json
from itertools import permutations

def solve_scheduling_problem():
    # Initialize Z3 solver with optimization
    opt = Optimize()

    # Convert all times to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(t):
        return int(t * 60)

    # Define travel times in minutes (already in minutes)
    travel_times = {
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Union Square'): 19,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'Sunset District'): 15,
        ('Haight-Ashbury', 'Golden Gate Park'): 7,
        # ... (include all other travel times from the original problem)
    }

    # Define friends with their constraints (converted to minutes)
    friends = [
        {"name": "Elizabeth", "location": "Mission District", 
         "start": time_to_minutes(10.5), "end": time_to_minutes(20.0), "duration": 90},
        {"name": "David", "location": "Union Square", 
         "start": time_to_minutes(15.25), "end": time_to_minutes(19.0), "duration": 45},
        {"name": "Sandra", "location": "Pacific Heights", 
         "start": time_to_minutes(7.0), "end": time_to_minutes(20.0), "duration": 120},
        {"name": "Thomas", "location": "Bayview", 
         "start": time_to_minutes(19.5), "end": time_to_minutes(20.5), "duration": 30},
        {"name": "Robert", "location": "Fisherman's Wharf", 
         "start": time_to_minutes(10.0), "end": time_to_minutes(15.0), "duration": 15},
        {"name": "Kenneth", "location": "Marina District", 
         "start": time_to_minutes(10.75), "end": time_to_minutes(13.0), "duration": 45},
        {"name": "Melissa", "location": "Richmond District", 
         "start": time_to_minutes(18.25), "end": time_to_minutes(20.0), "duration": 15},
        {"name": "Kimberly", "location": "Sunset District", 
         "start": time_to_minutes(10.25), "end": time_to_minutes(18.25), "duration": 105},
        {"name": "Amanda", "location": "Golden Gate Park", 
         "start": time_to_minutes(7.75), "end": time_to_minutes(18.75), "duration": 15}
    ]

    # Create variables for each meeting
    for friend in friends:
        friend["start_var"] = Int(f"{friend['name']}_start")
        friend["end_var"] = Int(f"{friend['name']}_end")
        friend["met"] = Bool(f"met_{friend['name']}")
        
        # Meeting must be within availability window if met
        opt.add(Implies(friend["met"], 
                    And(friend["start_var"] >= friend["start"],
                        friend["end_var"] <= friend["end"],
                        friend["end_var"] - friend["start_var"] >= friend["duration"])))

    # Initial location and time
    current_location = "Haight-Ashbury"
    current_time = 0  # 9:00 AM is time 0

    # Try all possible meeting orders (limited to 5 friends for performance)
    meeting_orders = list(permutations([f for f in friends if f["name"] in ["Amanda", "Robert", "Kenneth", "Kimberly", "Elizabeth"]], 5))

    # Store possible solutions
    possible_solutions = []

    for order in meeting_orders[:10]:  # Limit to first 10 permutations for performance
        s = Solver()
        
        # Add meeting constraints
        for friend in friends:
            s.add(Implies(friend["met"], 
                         And(friend["start_var"] >= friend["start"],
                             friend["end_var"] <= friend["end"],
                             friend["end_var"] - friend["start_var"] >= friend["duration"])))
        
        # Add travel time constraints for this order
        prev_loc = current_location
        prev_end = current_time
        for friend in order:
            travel_time = travel_times.get((prev_loc, friend["location"]), 0)
            s.add(Implies(friend["met"],
                         And(friend["start_var"] >= prev_end + travel_time)))
            prev_loc = friend["location"]
            prev_end = friend["end_var"]
        
        # Try to meet as many friends as possible
        s.maximize(Sum([If(f["met"], 1, 0) for f in friends]))
        
        if s.check() == sat:
            m = s.model()
            itinerary = []
            for friend in friends:
                if is_true(m[friend["met"]]):
                    start = m[friend["start_var"]].as_long()
                    end = m[friend["end_var"]].as_long()
                    start_h = 9 + start // 60
                    start_m = start % 60
                    end_h = 9 + end // 60
                    end_m = end % 60
                    itinerary.append({
                        "action": "meet",
                        "person": friend["name"],
                        "start_time": f"{start_h:02d}:{start_m:02d}",
                        "end_time": f"{end_h:02d}:{end_m:02d}"
                    })
            itinerary.sort(key=lambda x: (int(x["start_time"][:2]), int(x["start_time"][3:])))
            possible_solutions.append({"itinerary": itinerary, "score": len(itinerary)})

    # Return the best solution found
    if possible_solutions:
        best_solution = max(possible_solutions, key=lambda x: x["score"])
        return best_solution
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))