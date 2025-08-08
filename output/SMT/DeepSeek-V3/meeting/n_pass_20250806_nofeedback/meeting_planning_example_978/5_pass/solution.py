from z3 import *
import json
from itertools import permutations

def solve_scheduling_problem():
    # Initialize Z3 solver
    solver = Solver()

    # Define travel times between locations (in minutes)
    travel_times = {
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Pacific Heights"): 11,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "The Castro"): 25,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Pacific Heights"): 13,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "The Castro"): 20,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Pacific Heights"): 7,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "The Castro"): 21,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Pacific Heights"): 7,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "The Castro"): 22,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Pacific Heights"): 10,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "The Castro"): 16,
        ("Pacific Heights", "Embarcadero"): 10,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
        ("Pacific Heights", "Financial District"): 13,
        ("Pacific Heights", "Russian Hill"): 7,
        ("Pacific Heights", "Marina District"): 6,
        ("Pacific Heights", "Richmond District"): 12,
        ("Pacific Heights", "Haight-Ashbury"): 11,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "The Castro"): 16,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Pacific Heights"): 12,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Pacific Heights"): 11,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "The Castro"): 21,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "The Castro"): 16,
        ("The Castro", "Embarcadero"): 22,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Pacific Heights"): 16,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Nob Hill"): 16,
    }

    # Define friends' availability and meeting constraints
    friends = {
        "Stephanie": {
            "location": "Fisherman's Wharf",
            "start": 15 * 60 + 30,  # 15:30 in minutes
            "end": 22 * 60,          # 22:00 in minutes
            "duration": 30,          # 30 minutes
            "min_duration": 30       # Minimum required duration
        },
        "Lisa": {
            "location": "Financial District",
            "start": 10 * 60 + 45,   # 10:45 in minutes
            "end": 17 * 60 + 15,     # 17:15 in minutes
            "duration": 15,           # 15 minutes
            "min_duration": 15
        },
        "Melissa": {
            "location": "Russian Hill",
            "start": 17 * 60,        # 17:00 in minutes
            "end": 21 * 60 + 45,    # 21:45 in minutes
            "duration": 120,         # 120 minutes
            "min_duration": 60       # Can be reduced to 60 minutes
        },
        "Betty": {
            "location": "Marina District",
            "start": 10 * 60 + 45,   # 10:45 in minutes
            "end": 14 * 60 + 15,     # 14:15 in minutes
            "duration": 60,           # 60 minutes
            "min_duration": 30
        },
        "Sarah": {
            "location": "Richmond District",
            "start": 16 * 60 + 15,   # 16:15 in minutes
            "end": 19 * 60 + 30,     # 19:30 in minutes
            "duration": 105,          # 105 minutes
            "min_duration": 60
        },
        "Daniel": {
            "location": "Pacific Heights",
            "start": 18 * 60 + 30,  # 18:30 in minutes
            "end": 21 * 60 + 45,    # 21:45 in minutes
            "duration": 60,          # 60 minutes
            "min_duration": 30
        },
        "Joshua": {
            "location": "Haight-Ashbury",
            "start": 9 * 60,         # 09:00 in minutes
            "end": 15 * 60 + 30,     # 15:30 in minutes
            "duration": 15,           # 15 minutes
            "min_duration": 15
        },
        "Joseph": {
            "location": "Presidio",
            "start": 7 * 60,         # 07:00 in minutes
            "end": 13 * 60,          # 13:00 in minutes
            "duration": 45,           # 45 minutes
            "min_duration": 30
        },
        "Andrew": {
            "location": "Nob Hill",
            "start": 19 * 60 + 45,   # 19:45 in minutes
            "end": 22 * 60,          # 22:00 in minutes
            "duration": 105,         # 105 minutes
            "min_duration": 60
        },
        "John": {
            "location": "The Castro",
            "start": 13 * 60 + 15,   # 13:15 in minutes
            "end": 19 * 60 + 45,     # 19:45 in minutes
            "duration": 45,           # 45 minutes
            "min_duration": 30
        }
    }

    # Try multiple scheduling attempts with relaxed constraints
    for attempt in range(3):
        solver = Solver()
        
        # Create variables for each friend's meeting start and end times
        meeting_vars = {}
        for name in friends:
            start_var = Int(f"start_{name}")
            end_var = Int(f"end_{name}")
            meeting_vars[name] = (start_var, end_var)
            # Constrain the meeting to be within the friend's availability
            solver.add(start_var >= friends[name]["start"])
            solver.add(end_var <= friends[name]["end"])
            # Allow flexible duration between min and desired duration
            if attempt > 0:
                solver.add(end_var >= start_var + friends[name]["min_duration"])
                solver.add(end_var <= start_var + friends[name]["duration"])
            else:
                solver.add(end_var == start_var + friends[name]["duration"])

        # Initial location is Embarcadero at 9:00 AM (540 minutes)
        current_time = 540  # 9:00 AM in minutes
        current_location = "Embarcadero"

        # Try different meeting orders
        meeting_orders = [
            ["Joseph", "Joshua", "Betty", "Lisa", "John", "Sarah", "Daniel", "Melissa", "Andrew", "Stephanie"],
            ["Joshua", "Joseph", "Betty", "Lisa", "John", "Sarah", "Daniel", "Melissa", "Andrew", "Stephanie"],
            ["Joseph", "Betty", "Lisa", "Joshua", "John", "Sarah", "Daniel", "Melissa", "Andrew", "Stephanie"]
        ]

        for meeting_order in meeting_orders[:attempt+1]:
            # Add constraints for travel times between meetings
            for i in range(len(meeting_order)):
                name = meeting_order[i]
                start_var, end_var = meeting_vars[name]
                # The meeting must start after the previous meeting ends plus travel time
                if i == 0:
                    # First meeting must start after current_time + travel time
                    solver.add(start_var >= current_time + travel_times[(current_location, friends[name]["location"])])
                else:
                    prev_name = meeting_order[i-1]
                    prev_end_var = meeting_vars[prev_name][1]
                    solver.add(start_var >= prev_end_var + travel_times[(friends[prev_name]["location"], friends[name]["location"])])

            # Check if the constraints are satisfiable
            if solver.check() == sat:
                model = solver.model()
                itinerary = []
                for name in meeting_order:
                    start_var, end_var = meeting_vars[name]
                    start_time = model[start_var].as_long()
                    end_time = model[end_var].as_long()
                    # Convert minutes to HH:MM format
                    start_hh = start_time // 60
                    start_mm = start_time % 60
                    end_hh = end_time // 60
                    end_mm = end_time % 60
                    itinerary.append({
                        "action": "meet",
                        "person": name,
                        "start_time": f"{start_hh:02d}:{start_mm:02d}",
                        "end_time": f"{end_hh:02d}:{end_mm:02d}"
                    })
                return {"itinerary": itinerary}

            solver.reset()

        # If no solution found, relax constraints further
        for name in friends:
            if friends[name]["min_duration"] > 15:
                friends[name]["min_duration"] -= 15

    return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))