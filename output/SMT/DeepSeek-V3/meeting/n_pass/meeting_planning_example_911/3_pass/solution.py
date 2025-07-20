from z3 import *
import json

def solve_scheduling():
    # Initialize solver
    s = Solver()

    # Define friends and their details
    friends = {
        "Steven": {"location": "North Beach", "start": 17*60 + 30, "end": 20*60 + 30, "duration": 15},
        "Sarah": {"location": "Golden Gate Park", "start": 17*60 + 0, "end": 19*60 + 15, "duration": 75},
        "Brian": {"location": "Embarcadero", "start": 14*60 + 15, "end": 16*60 + 0, "duration": 105},
        "Stephanie": {"location": "Haight-Ashbury", "start": 10*60 + 15, "end": 12*60 + 15, "duration": 75},
        "Melissa": {"location": "Richmond District", "start": 14*60 + 0, "end": 19*60 + 30, "duration": 30},
        "Nancy": {"location": "Nob Hill", "start": 8*60 + 15, "end": 12*60 + 45, "duration": 90},
        "David": {"location": "Marina District", "start": 11*60 + 15, "end": 13*60 + 15, "duration": 120},
        "James": {"location": "Presidio", "start": 15*60 + 0, "end": 18*60 + 15, "duration": 120},
        "Elizabeth": {"location": "Union Square", "start": 11*60 + 30, "end": 21*60 + 0, "duration": 60},
        "Robert": {"location": "Financial District", "start": 13*60 + 15, "end": 15*60 + 15, "duration": 45}
    }

    # Define travel times (in minutes) between locations. The Castro is starting point.
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
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Financial District"): 8,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Haight-Ashbury"): 7,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Financial District"): 26,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Financial District"): 5,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Financial District"): 22,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Financial District"): 9,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Financial District"): 17,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Financial District"): 23,
        ("Union Square", "Financial District"): 9
    }

    # Create variables for each friend's meeting start and end times (in minutes since 9:00 AM)
    variables = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        variables[name] = {'start': start_var, 'end': end_var}

    # Add constraints for each friend
    for name in friends:
        friend = friends[name]
        s.add(variables[name]['start'] >= friend['start'] - 9*60)  # Convert to minutes since 9:00 AM
        s.add(variables[name]['end'] <= friend['end'] - 9*60)
        s.add(variables[name]['end'] - variables[name]['start'] >= friend['duration'])

    # Define the order of meetings using a list of friends
    order = ["Nancy", "Stephanie", "David", "Elizabeth", "Robert", "Brian", "James", "Melissa", "Sarah", "Steven"]

    # Add travel time constraints between consecutive meetings
    current_location = "The Castro"
    current_time = 0
    for name in order:
        friend_loc = friends[name]["location"]
        travel_time = travel_times.get((current_location, friend_loc), 0)
        s.add(variables[name]['start'] >= current_time + travel_time)
        current_time = variables[name]['end']
        current_location = friend_loc

    # Check if the schedule is feasible
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for name in order:
            start = m[variables[name]['start']].as_long()
            end = m[variables[name]['end']].as_long()
            start_time = f"{(start + 9*60) // 60:02d}:{(start + 9*60) % 60:02d}"
            end_time = f"{(end + 9*60) // 60:02d}:{(end + 9*60) % 60:02d}"
            itinerary.append({"action": "meet", "person": name, "start_time": start_time, "end_time": end_time})
        return {"itinerary": itinerary}
    else:
        return {"error": "No feasible schedule found"}

# Solve and print the result
result = solve_scheduling()
print(json.dumps(result, indent=2))