import z3
from datetime import datetime, timedelta

def solve_scheduling_problem():
    # Initialize Z3 solver
    solver = z3.Solver()

    # Define the locations and their respective friends and time windows
    friends = {
        "Daniel": {"location": "Nob Hill", "start": "08:15", "end": "11:00", "duration": 15},
        "Timothy": {"location": "Pacific Heights", "start": "12:00", "end": "18:00", "duration": 90},
        "Kevin": {"location": "Chinatown", "start": "12:00", "end": "19:00", "duration": 30},
        "Betty": {"location": "Richmond District", "start": "13:15", "end": "15:45", "duration": 30},
        "Steven": {"location": "Marina District", "start": "16:30", "end": "20:45", "duration": 90},
        "Lisa": {"location": "The Castro", "start": "19:15", "end": "21:15", "duration": 120},
        "Ashley": {"location": "Golden Gate Park", "start": "20:45", "end": "21:45", "duration": 60},
        "Elizabeth": {"location": "Presidio", "start": "21:15", "end": "22:15", "duration": 45}
    }

    # Travel times dictionary (from_location, to_location) -> minutes
    travel_times = {
        ("Mission District", "The Castro"): 7,
        ("Mission District", "Nob Hill"): 12,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Marina District"): 19,
        ("Mission District", "Pacific Heights"): 16,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "Richmond District"): 20,
        ("The Castro", "Mission District"): 7,
        ("The Castro", "Nob Hill"): 16,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Golden Gate Park"): 11,
        ("The Castro", "Chinatown"): 22,
        ("The Castro", "Richmond District"): 16,
        ("Nob Hill", "Mission District"): 13,
        ("Nob Hill", "The Castro"): 17,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Richmond District"): 14,
        ("Presidio", "Mission District"): 26,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Richmond District"): 7,
        ("Marina District", "Mission District"): 20,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Richmond District"): 11,
        ("Pacific Heights", "Mission District"): 15,
        ("Pacific Heights", "The Castro"): 16,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Golden Gate Park"): 15,
        ("Pacific Heights", "Chinatown"): 11,
        ("Pacific Heights", "Richmond District"): 12,
        ("Golden Gate Park", "Mission District"): 17,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Pacific Heights"): 16,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Chinatown", "Mission District"): 17,
        ("Chinatown", "The Castro"): 22,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Marina District"): 12,
        ("Chinatown", "Pacific Heights"): 10,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Richmond District"): 20,
        ("Richmond District", "Mission District"): 20,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Chinatown"): 20
    }

    # Convert time strings to minutes since 9:00 AM (540 minutes)
    def time_to_minutes(time_str):
        h, m = map(int, time_str.split(':'))
        return h * 60 + m

    # Convert minutes back to time string
    def minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    # Initialize variables for each friend's meeting start and end times
    meeting_vars = {}
    for friend in friends:
        start_var = z3.Int(f"start_{friend}")
        end_var = z3.Int(f"end_{friend}")
        meeting_vars[friend] = (start_var, end_var)

    # Current location starts at Mission District at 9:00 AM (540 minutes)
    current_location = "Mission District"
    current_time = 540  # 9:00 AM in minutes

    # Order in which we'll try to meet friends (this is a heuristic to help the solver)
    meeting_order = ["Daniel", "Timothy", "Kevin", "Betty", "Steven", "Lisa", "Ashley", "Elizabeth"]

    # Constraints for each meeting
    for friend in meeting_order:
        start_var, end_var = meeting_vars[friend]
        info = friends[friend]
        start_window = time_to_minutes(info["start"])
        end_window = time_to_minutes(info["end"])
        duration = info["duration"]

        # Meeting must be within the friend's availability window
        solver.add(start_var >= start_window)
        solver.add(end_var <= end_window)
        solver.add(end_var == start_var + duration)

        # Travel time from current location to friend's location
        travel_time = travel_times.get((current_location, info["location"]), 0)
        solver.add(start_var >= current_time + travel_time)

        # Update current location and time after the meeting
        current_location = info["location"]
        current_time = end_var

    # Ensure no overlapping meetings (though the order should prevent this)
    for i in range(len(meeting_order)):
        for j in range(i + 1, len(meeting_order)):
            friend1 = meeting_order[i]
            friend2 = meeting_order[j]
            start1, end1 = meeting_vars[friend1]
            start2, end2 = meeting_vars[friend2]
            solver.add(z3.Or(end1 <= start2, end2 <= start1))

    # Check if the problem is satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary = []
        for friend in meeting_order:
            start_var, end_var = meeting_vars[friend]
            start_time = model.eval(start_var).as_long()
            end_time = model.eval(end_var).as_long()
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": minutes_to_time(start_time),
                "end_time": minutes_to_time(end_time)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(solution)