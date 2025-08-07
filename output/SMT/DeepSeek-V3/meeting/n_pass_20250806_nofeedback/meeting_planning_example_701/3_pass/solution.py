import z3

def solve_scheduling_problem():
    solver = z3.Solver()

    # Friends data with time windows and durations
    friends = {
        "Daniel": {"location": "Nob Hill", "start": 495, "end": 660, "duration": 15},  # 8:15-11:00
        "Timothy": {"location": "Pacific Heights", "start": 720, "end": 1080, "duration": 90},  # 12:00-18:00
        "Kevin": {"location": "Chinatown", "start": 720, "end": 1140, "duration": 30},  # 12:00-19:00
        "Betty": {"location": "Richmond District", "start": 795, "end": 945, "duration": 30},  # 13:15-15:45
        "Steven": {"location": "Marina District", "start": 990, "end": 1245, "duration": 90},  # 16:30-20:45
        "Lisa": {"location": "The Castro", "start": 1155, "end": 1275, "duration": 120},  # 19:15-21:15
        "Ashley": {"location": "Golden Gate Park", "start": 1245, "end": 1305, "duration": 60},  # 20:45-21:45
        "Elizabeth": {"location": "Presidio", "start": 1275, "end": 1335, "duration": 45}  # 21:15-22:15
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

    # Define the sequence of meetings (this is a heuristic to help the solver)
    meeting_sequence = ["Daniel", "Timothy", "Kevin", "Betty", "Steven", "Lisa", "Ashley", "Elizabeth"]

    # Add sequencing constraints with travel times
    current_location = "Mission District"
    current_time = 540  # Starting at 9:00 AM (540 minutes)

    for i in range(len(meeting_sequence)):
        friend = meeting_sequence[i]
        next_location = friends[friend]["location"]
        
        # Travel time from current location to next meeting
        travel_time = travel_times.get((current_location, next_location), 0)
        
        # Ensure we have enough time to travel and meet
        solver.add(start_vars[friend] >= current_time + travel_time)
        
        # Update current location and time
        current_location = next_location
        current_time = end_vars[friend]

    # Ensure no overlapping meetings
    for i in range(len(meeting_sequence)):
        for j in range(i+1, len(meeting_sequence)):
            friend1 = meeting_sequence[i]
            friend2 = meeting_sequence[j]
            solver.add(z3.Or(
                end_vars[friend1] <= start_vars[friend2],
                end_vars[friend2] <= start_vars[friend1]
            ))

    # Check for solution
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary = []
        for friend in meeting_sequence:
            start = model.eval(start_vars[friend]).as_long()
            end = model.eval(end_vars[friend]).as_long()
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": f"{start//60:02d}:{start%60:02d}",
                "end_time": f"{end//60:02d}:{end%60:02d}"
            })
        return {"itinerary": itinerary}
    else:
        # If no solution found, try relaxing constraints
        print("No solution found with current constraints")
        return {"itinerary": []}

solution = solve_scheduling_problem()
print("SOLUTION:")
print(solution)