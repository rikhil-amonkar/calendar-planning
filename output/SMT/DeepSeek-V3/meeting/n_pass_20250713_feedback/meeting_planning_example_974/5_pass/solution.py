from z3 import *

def solve_scheduling():
    s = Solver()

    # Define friends data
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

    # Travel times in hours
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
        ("Presidio", "Nob Hill"): 18/60,
        ("Presidio", "Pacific Heights"): 11/60,
        ("Presidio", "Mission District"): 26/60,
        ("Presidio", "Marina District"): 11/60,
        ("Presidio", "North Beach"): 18/60,
        ("Presidio", "Russian Hill"): 14/60,
        ("Presidio", "Richmond District"): 7/60,
        ("Presidio", "Embarcadero"): 20/60,
        ("Presidio", "Alamo Square"): 19/60,
        ("Nob Hill", "Pacific Heights"): 8/60,
        ("Nob Hill", "Mission District"): 13/60,
        ("Nob Hill", "Marina District"): 11/60,
        ("Nob Hill", "North Beach"): 8/60,
        ("Nob Hill", "Russian Hill"): 5/60,
        ("Nob Hill", "Richmond District"): 14/60,
        ("Nob Hill", "Embarcadero"): 9/60,
        ("Nob Hill", "Alamo Square"): 11/60,
        ("Pacific Heights", "Mission District"): 15/60,
        ("Pacific Heights", "Marina District"): 6/60,
        ("Pacific Heights", "North Beach"): 9/60,
        ("Pacific Heights", "Russian Hill"): 7/60,
        ("Pacific Heights", "Richmond District"): 12/60,
        ("Pacific Heights", "Embarcadero"): 10/60,
        ("Pacific Heights", "Alamo Square"): 10/60,
        ("Mission District", "Marina District"): 19/60,
        ("Mission District", "North Beach"): 17/60,
        ("Mission District", "Russian Hill"): 15/60,
        ("Mission District", "Richmond District"): 20/60,
        ("Mission District", "Embarcadero"): 19/60,
        ("Mission District", "Alamo Square"): 11/60,
        ("Marina District", "North Beach"): 11/60,
        ("Marina District", "Russian Hill"): 8/60,
        ("Marina District", "Richmond District"): 11/60,
        ("Marina District", "Embarcadero"): 14/60,
        ("Marina District", "Alamo Square"): 15/60,
        ("North Beach", "Russian Hill"): 4/60,
        ("North Beach", "Richmond District"): 18/60,
        ("North Beach", "Embarcadero"): 6/60,
        ("North Beach", "Alamo Square"): 16/60,
        ("Russian Hill", "Richmond District"): 14/60,
        ("Russian Hill", "Embarcadero"): 8/60,
        ("Russian Hill", "Alamo Square"): 15/60,
        ("Richmond District", "Embarcadero"): 19/60,
        ("Richmond District", "Alamo Square"): 13/60,
        ("Embarcadero", "Alamo Square"): 19/60
    }

    # Create variables
    meeting_start = {name: Real(f'start_{name}') for name in friends}
    meeting_end = {name: Real(f'end_{name}') for name in friends}
    meet = {name: Bool(f'meet_{name}') for name in friends}
    position = {name: Int(f'pos_{name}') for name in friends}  # Position in sequence

    # Constraints
    for name in friends:
        friend = friends[name]
        s.add(Implies(meet[name], meeting_start[name] >= friend["start"]))
        s.add(Implies(meet[name], meeting_end[name] <= friend["end"]))
        s.add(Implies(meet[name], meeting_end[name] - meeting_start[name] >= friend["duration"]))
        
        # Initial travel from Sunset District
        travel_time = travel_times[("Sunset District", friend["location"])]
        s.add(Implies(meet[name], meeting_start[name] >= 9.0 + travel_time))

    # Exactly 7 friends must be met
    s.add(Sum([If(meet[name], 1, 0) for name in friends]) == 7)

    # Sequence constraints
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                # If both are met, they must have distinct positions
                s.add(Implies(And(meet[name1], meet[name2]), position[name1] != position[name2]))
                
                # If name1 comes before name2, enforce travel time
                s.add(Implies(And(meet[name1], meet[name2], position[name1] < position[name2]),
                             meeting_start[name2] >= meeting_end[name1] + travel_times[(friends[name1]["location"], friends[name2]["location"])]))

    # Try to find a solution
    if s.check() == sat:
        m = s.model()
        schedule = []
        for name in friends:
            if is_true(m[meet[name]]):
                start = m[meeting_start[name]].as_fraction()
                end = m[meeting_end[name]].as_fraction()
                pos = m[position[name]].as_long()
                schedule.append((pos, name, float(start), float(end), friends[name]["location"]))
        
        schedule.sort()
        return [(name, start, end, loc) for (pos, name, start, end, loc) in schedule]
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
    print("No feasible schedule found that meets exactly 7 people with all constraints.")