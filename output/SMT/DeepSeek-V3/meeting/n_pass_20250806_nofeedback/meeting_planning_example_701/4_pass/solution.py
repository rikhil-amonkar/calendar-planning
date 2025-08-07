import z3
from itertools import combinations

def solve_scheduling_problem():
    solver = z3.Solver()

    # Convert time strings to minutes since midnight
    def time_to_min(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

    # Friends data with time windows and durations (all times in minutes since midnight)
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

    # Create variables to represent the meeting order
    n = len(friends)
    position = {friend: z3.Int(f"pos_{friend}") for friend in friends}
    for friend in friends:
        solver.add(position[friend] >= 0)
        solver.add(position[friend] < n)

    # All meetings must have unique positions
    solver.add(z3.Distinct([position[friend] for friend in friends]))

    # Add travel time constraints based on ordering
    for f1, f2 in combinations(friends.keys(), 2):
        # If f1 comes before f2 in the order
        f1_before_f2 = position[f1] < position[f2]
        
        # Get travel time between locations
        loc1 = friends[f1]["location"]
        loc2 = friends[f2]["location"]
        travel_time = travel_times.get((loc1, loc2), 0)
        
        # Add constraints for both possible orderings
        solver.add(z3.Implies(f1_before_f2, start_vars[f2] >= end_vars[f1] + travel_time))
        solver.add(z3.Implies(z3.Not(f1_before_f2), start_vars[f1] >= end_vars[f2] + travel_times.get((loc2, loc1), 0)))

    # Starting point: Mission District at 9:00 AM (540 minutes)
    first_meeting = z3.Int("first_meeting")
    solver.add(first_meeting >= 0)
    solver.add(first_meeting < n)
    for friend in friends:
        solver.add(z3.Implies(position[friend] == first_meeting, 
                        start_vars[friend] >= 540 + travel_times.get(("Mission District", friends[friend]["location"]), 0)))

    # Check for solution
    if solver.check() == z3.sat:
        model = solver.model()
        # Get the schedule in order
        schedule = []
        for i in range(n):
            for friend in friends:
                if model.eval(position[friend]).as_long() == i:
                    start = model.eval(start_vars[friend]).as_long()
                    end = model.eval(end_vars[friend]).as_long()
                    schedule.append({
                        "action": "meet",
                        "person": friend,
                        "start_time": f"{start//60:02d}:{start%60:02d}",
                        "end_time": f"{end//60:02d}:{end%60:02d}",
                        "location": friends[friend]["location"]
                    })
                    break
        
        return {"itinerary": schedule}
    else:
        print("No valid schedule found that meets all constraints")
        return {"itinerary": []}

solution = solve_scheduling_problem()
print("SOLUTION:")
print(solution)