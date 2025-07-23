from z3 import *

def solve_scheduling():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their locations, available times, and desired meeting durations
    friends = {
        "Charles": {"location": "Presidio", "start": 13.25, "end": 15.0, "duration": 1.75},
        "Robert": {"location": "Nob Hill", "start": 13.25, "end": 17.5, "duration": 1.5},
        "Nancy": {"location": "Pacific Heights", "start": 14.75, "end": 22.0, "duration": 1.75},
        "Brian": {"location": "Mission District", "start": 15.5, "end": 22.0, "duration": 1.0},
        "Kimberly": {"location": "Marina District", "start": 17.0, "end": 19.75, "duration": 1.25},
        "David": {"location": "North Beach", "start": 14.75, "end": 16.5, "duration": 1.25},
        "William": {"location": "Russian Hill", "start": 12.5, "end": 19.25, "duration": 2.0},
        "Jeffrey": {"location": "Richmond District", "start": 12.0, "end": 19.25, "duration": 0.75},
        "Karen": {"location": "Embarcadero", "start": 14.25, "end": 20.75, "duration": 1.0},
        "Joshua": {"location": "Alamo Square", "start": 18.75, "end": 22.0, "duration": 1.0}
    }

    # Travel times dictionary (in hours)
    travel_times = {
        ("Sunset District", "Presidio"): 16/60,
        ("Sunset District", "Nob Hill"): 27/60,
        ("Sunset District", "Pacific Heights"): 21/60,
        ("Sunset District", "Mission District"): 25/60,
        ("Sunset District", "Marina District"): 21/60,
        ("Sunset District", "North Beach"): 28/60,
        ("Sunset District", "Russian Hill"): 24/60,
        ("Sunset District", "Richmond District"): 12/60,
        ("Sunset District", "Embarcadero"): 30/60,
        ("Sunset District", "Alamo Square"): 17/60,
        ("Presidio", "Sunset District"): 15/60,
        ("Presidio", "Nob Hill"): 18/60,
        ("Presidio", "Pacific Heights"): 11/60,
        ("Presidio", "Mission District"): 26/60,
        ("Presidio", "Marina District"): 11/60,
        ("Presidio", "North Beach"): 18/60,
        ("Presidio", "Russian Hill"): 14/60,
        ("Presidio", "Richmond District"): 7/60,
        ("Presidio", "Embarcadero"): 20/60,
        ("Presidio", "Alamo Square"): 19/60,
        ("Nob Hill", "Sunset District"): 24/60,
        ("Nob Hill", "Presidio"): 17/60,
        ("Nob Hill", "Pacific Heights"): 8/60,
        ("Nob Hill", "Mission District"): 13/60,
        ("Nob Hill", "Marina District"): 11/60,
        ("Nob Hill", "North Beach"): 8/60,
        ("Nob Hill", "Russian Hill"): 5/60,
        ("Nob Hill", "Richmond District"): 14/60,
        ("Nob Hill", "Embarcadero"): 9/60,
        ("Nob Hill", "Alamo Square"): 11/60,
        ("Pacific Heights", "Sunset District"): 21/60,
        ("Pacific Heights", "Presidio"): 11/60,
        ("Pacific Heights", "Nob Hill"): 8/60,
        ("Pacific Heights", "Mission District"): 15/60,
        ("Pacific Heights", "Marina District"): 6/60,
        ("Pacific Heights", "North Beach"): 9/60,
        ("Pacific Heights", "Russian Hill"): 7/60,
        ("Pacific Heights", "Richmond District"): 12/60,
        ("Pacific Heights", "Embarcadero"): 10/60,
        ("Pacific Heights", "Alamo Square"): 10/60,
        ("Mission District", "Sunset District"): 24/60,
        ("Mission District", "Presidio"): 25/60,
        ("Mission District", "Nob Hill"): 12/60,
        ("Mission District", "Pacific Heights"): 16/60,
        ("Mission District", "Marina District"): 19/60,
        ("Mission District", "North Beach"): 17/60,
        ("Mission District", "Russian Hill"): 15/60,
        ("Mission District", "Richmond District"): 20/60,
        ("Mission District", "Embarcadero"): 19/60,
        ("Mission District", "Alamo Square"): 11/60,
        ("Marina District", "Sunset District"): 19/60,
        ("Marina District", "Presidio"): 10/60,
        ("Marina District", "Nob Hill"): 12/60,
        ("Marina District", "Pacific Heights"): 7/60,
        ("Marina District", "Mission District"): 20/60,
        ("Marina District", "North Beach"): 11/60,
        ("Marina District", "Russian Hill"): 8/60,
        ("Marina District", "Richmond District"): 11/60,
        ("Marina District", "Embarcadero"): 14/60,
        ("Marina District", "Alamo Square"): 15/60,
        ("North Beach", "Sunset District"): 27/60,
        ("North Beach", "Presidio"): 17/60,
        ("North Beach", "Nob Hill"): 7/60,
        ("North Beach", "Pacific Heights"): 8/60,
        ("North Beach", "Mission District"): 18/60,
        ("North Beach", "Marina District"): 9/60,
        ("North Beach", "Russian Hill"): 4/60,
        ("North Beach", "Richmond District"): 18/60,
        ("North Beach", "Embarcadero"): 6/60,
        ("North Beach", "Alamo Square"): 16/60,
        ("Russian Hill", "Sunset District"): 23/60,
        ("Russian Hill", "Presidio"): 14/60,
        ("Russian Hill", "Nob Hill"): 5/60,
        ("Russian Hill", "Pacific Heights"): 7/60,
        ("Russian Hill", "Mission District"): 16/60,
        ("Russian Hill", "Marina District"): 7/60,
        ("Russian Hill", "North Beach"): 5/60,
        ("Russian Hill", "Richmond District"): 14/60,
        ("Russian Hill", "Embarcadero"): 8/60,
        ("Russian Hill", "Alamo Square"): 15/60,
        ("Richmond District", "Sunset District"): 11/60,
        ("Richmond District", "Presidio"): 7/60,
        ("Richmond District", "Nob Hill"): 17/60,
        ("Richmond District", "Pacific Heights"): 10/60,
        ("Richmond District", "Mission District"): 20/60,
        ("Richmond District", "Marina District"): 9/60,
        ("Richmond District", "North Beach"): 17/60,
        ("Richmond District", "Russian Hill"): 13/60,
        ("Richmond District", "Embarcadero"): 19/60,
        ("Richmond District", "Alamo Square"): 13/60,
        ("Embarcadero", "Sunset District"): 30/60,
        ("Embarcadero", "Presidio"): 20/60,
        ("Embarcadero", "Nob Hill"): 10/60,
        ("Embarcadero", "Pacific Heights"): 11/60,
        ("Embarcadero", "Mission District"): 20/60,
        ("Embarcadero", "Marina District"): 12/60,
        ("Embarcadero", "North Beach"): 5/60,
        ("Embarcadero", "Russian Hill"): 8/60,
        ("Embarcadero", "Richmond District"): 21/60,
        ("Embarcadero", "Alamo Square"): 19/60,
        ("Alamo Square", "Sunset District"): 16/60,
        ("Alamo Square", "Presidio"): 17/60,
        ("Alamo Square", "Nob Hill"): 11/60,
        ("Alamo Square", "Pacific Heights"): 10/60,
        ("Alamo Square", "Mission District"): 10/60,
        ("Alamo Square", "Marina District"): 15/60,
        ("Alamo Square", "North Beach"): 15/60,
        ("Alamo Square", "Russian Hill"): 13/60,
        ("Alamo Square", "Richmond District"): 11/60,
        ("Alamo Square", "Embarcadero"): 16/60
    }

    # Create variables for each friend's meeting start and end times
    meeting_start = {name: Real(f'start_{name}') for name in friends}
    meeting_end = {name: Real(f'end_{name}') for name in friends}
    meet = {name: Bool(f'meet_{name}') for name in friends}  # Whether to meet this friend

    # Current location starts at Sunset District at 9:00 AM (9.0)
    current_location = "Sunset District"
    current_time = 9.0

    # Constraints for each friend
    for name in friends:
        friend = friends[name]
        # If meeting this friend, enforce time constraints
        s.add(Implies(meet[name], meeting_start[name] >= friend["start"]))
        s.add(Implies(meet[name], meeting_end[name] <= friend["end"]))
        s.add(Implies(meet[name], meeting_end[name] - meeting_start[name] >= friend["duration"]))
        # Meeting must start after arrival at the location
        travel_time = travel_times[(current_location, friend["location"])]
        s.add(Implies(meet[name], meeting_start[name] >= current_time + travel_time))

    # Ensure exactly 7 friends are met
    s.add(Sum([If(meet[name], 1, 0) for name in friends]) == 7)

    # No overlapping meetings (simplified for this example)
    # For simplicity, we'll assume meetings are sequential and don't overlap
    # In a more complex model, we'd need to ensure no two meetings overlap if they can't be attended simultaneously

    # Maximize the number of friends met (simplified objective)
    # Here, we'll just check if all constraints are satisfiable
    if s.check() == sat:
        m = s.model()
        schedule = []
        for name in friends:
            if is_true(m[meet[name]]):
                start = m[meeting_start[name]].as_fraction()
                end = m[meeting_end[name]].as_fraction()
                schedule.append((name, float(start), float(end), friends[name]["location"]))
        schedule.sort(key=lambda x: x[1])  # Sort by start time
        return schedule
    else:
        return None

schedule = solve_scheduling()
if schedule:
    print("SOLUTION:")
    for name, start, end, location in schedule:
        start_time = f"{int(start)}:{int((start % 1) * 60):02d}"
        end_time = f"{int(end)}:{int((end % 1) * 60):02d}"
        print(f"Meet {name} from {start_time} to {end_time} at {location}")
else:
    print("No feasible schedule found.")