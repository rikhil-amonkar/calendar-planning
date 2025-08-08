import z3
from itertools import permutations

def solve_scheduling_problem():
    solver = z3.Solver()

    # Convert time strings to minutes since midnight
    def time_to_min(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

    # Friends data with time windows and durations
    friends = {
        "Daniel": {"location": "Nob Hill", "start": time_to_min("08:15"), "end": time_to_min("11:00"), "duration": 15},
        "Timothy": {"location": "Pacific Heights", "start": time_to_min("12:00"), "end": time_to_min("18:00"), "duration": 90},
        "Kevin": {"location": "Chinatown", "start": time_to_min("12:00"), "end": time_to_min("19:00"), "duration": 30},
        "Betty": {"location": "Richmond District", "start": time_to_min("13:15"), "end": time_to_min("15:45"), "duration": 30},
        "Steven": {"location": "Marina District", "start": time_to_min("16:30"), "end": time_to_min("20:45"), "duration": 90},
        "Lisa": {"location": "The Castro", "start": time_to_min("19:15"), "end": time_to_min("21:15"), "duration": 120},
        "Ashley": {"location": "Golden Gate Park", "start": time_to_min("20:45"), "end": time_to_min("21:45"), "duration": 60},
        "Elizabeth": {"location": "Presidio", "start": time_to_min("21:15"), "end": time_to_min("22:15"), "duration": 45}
    }

    # Travel times between locations (in minutes)
    travel_times = {
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Richmond District"): 20,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Presidio"): 25,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "The Castro"): 16,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Presidio"): 17,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Presidio"): 11,
        ("Chinatown", "Richmond District"): 20,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Presidio"): 19,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Presidio"): 7,
        ("Marina District", "The Castro"): 21,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Presidio"): 10,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Presidio"): 20,
        ("Golden Gate Park", "Presidio"): 11
    }

    # Create variables for meeting start times
    start_vars = {friend: z3.Int(f"start_{friend}") for friend in friends}
    end_vars = {friend: z3.Int(f"end_{friend}") for friend in friends}

    # Basic constraints for each meeting
    for friend in friends:
        info = friends[friend]
        solver.add(start_vars[friend] >= info["start"])
        solver.add(end_vars[friend] <= info["end"])
        solver.add(end_vars[friend] == start_vars[friend] + info["duration"])

    # Try all possible meeting orders (since Z3 struggles with permutations)
    # We'll limit to reasonable permutations that might work
    possible_orders = [
        ["Daniel", "Timothy", "Kevin", "Betty", "Steven", "Lisa", "Ashley", "Elizabeth"],
        ["Daniel", "Timothy", "Betty", "Kevin", "Steven", "Lisa", "Ashley", "Elizabeth"],
        ["Daniel", "Kevin", "Timothy", "Betty", "Steven", "Lisa", "Ashley", "Elizabeth"],
        ["Daniel", "Betty", "Timothy", "Kevin", "Steven", "Lisa", "Ashley", "Elizabeth"]
    ]

    solution_found = False
    best_schedule = []

    for order in possible_orders:
        temp_solver = z3.Solver()
        temp_solver.add(solver.assertions())
        
        # Add ordering constraints
        current_location = "Mission District"
        current_time = 540  # 9:00 AM
        
        for i in range(len(order)):
            friend = order[i]
            next_location = friends[friend]["location"]
            travel_time = travel_times.get((current_location, next_location), 0)
            
            temp_solver.add(start_vars[friend] >= current_time + travel_time)
            
            current_location = next_location
            current_time = end_vars[friend]
        
        # Check if this order works
        if temp_solver.check() == z3.sat:
            model = temp_solver.model()
            schedule = []
            for friend in order:
                start = model.eval(start_vars[friend]).as_long()
                end = model.eval(end_vars[friend]).as_long()
                schedule.append({
                    "action": "meet",
                    "person": friend,
                    "start_time": f"{start//60:02d}:{start%60:02d}",
                    "end_time": f"{end//60:02d}:{end%60:02d}",
                    "location": friends[friend]["location"]
                })
            best_schedule = schedule
            solution_found = True
            break

    if solution_found:
        return {"itinerary": best_schedule}
    else:
        print("No valid schedule found with the tested meeting orders")
        return {"itinerary": []}

solution = solve_scheduling_problem()
print("SOLUTION:")
print(solution)