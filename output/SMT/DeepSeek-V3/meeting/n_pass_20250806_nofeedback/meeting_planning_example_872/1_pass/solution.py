from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Friends and their details
    friends = {
        "Karen": {"location": "Haight-Ashbury", "start": 1260, "end": 1305, "min_duration": 45},
        "Jessica": {"location": "Nob Hill", "start": 825, "end": 1260, "min_duration": 90},
        "Brian": {"location": "Russian Hill", "start": 930, "end": 1305, "min_duration": 60},
        "Kenneth": {"location": "North Beach", "start": 585, "end": 1260, "min_duration": 30},
        "Jason": {"location": "Chinatown", "start": 495, "end": 705, "min_duration": 75},
        "Stephanie": {"location": "Union Square", "start": 885, "end": 1125, "min_duration": 105},
        "Kimberly": {"location": "Embarcadero", "start": 585, "end": 1170, "min_duration": 75},
        "Steven": {"location": "Financial District", "start": 435, "end": 1290, "min_duration": 60},
        "Mark": {"location": "Marina District", "start": 615, "end": 780, "min_duration": 75}
    }

    # Travel times dictionary (simplified for the model)
    travel_times = {
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Marina District"): 11,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Nob Hill"): 15,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "North Beach"): 19,
        ("Haight-Ashbury", "Chinatown"): 19,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Embarcadero"): 20,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "Haight-Ashbury"): 13,
        ("Nob Hill", "Russian Hill"): 5,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Chinatown"): 6,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "Marina District"): 11,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "Nob Hill"): 5,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Chinatown"): 9,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Embarcadero"): 8,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Marina District"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Haight-Ashbury"): 18,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Marina District"): 9,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Haight-Ashbury"): 19,
        ("Chinatown", "Nob Hill"): 9,
        ("Chinatown", "Russian Hill"): 7,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Union Square"): 7,
        ("Chinatown", "Embarcadero"): 5,
        ("Chinatown", "Financial District"): 5,
        ("Chinatown", "Marina District"): 12,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Chinatown"): 7,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Marina District"): 18,
        ("Embarcadero", "Presidio"): 20,
        ("Embarcadero", "Haight-Ashbury"): 21,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Russian Hill"): 8,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Chinatown"): 7,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "Marina District"): 12,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Chinatown"): 5,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "Marina District"): 15,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Chinatown"): 15,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Financial District"): 17
    }

    # Create variables for each friend's meeting start and end times
    meeting_vars = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        meeting_vars[name] = {'start': start_var, 'end': end_var}

    # Constraints for each meeting's duration and availability
    for name in friends:
        info = friends[name]
        s.add(meeting_vars[name]['start'] >= info['start'])
        s.add(meeting_vars[name]['end'] <= info['end'])
        s.add(meeting_vars[name]['end'] - meeting_vars[name]['start'] >= info['min_duration'])

    # Additional constraints to ensure meetings don't overlap and travel times are respected
    # Since the problem is complex, we'll prioritize meeting as many friends as possible
    # by selecting a subset that can fit into the schedule without overlaps.

    # We'll try to meet all friends, but the solver will find a feasible subset.
    # To maximize the number of friends met, we'll use a pseudo-Boolean approach.

    # Create a Boolean for each friend indicating whether they are met
    met = {name: Bool(f'met_{name}') for name in friends}

    # If a friend is met, their meeting times must be set
    for name in friends:
        s.add(Implies(met[name], And(
            meeting_vars[name]['start'] >= friends[name]['start'],
            meeting_vars[name]['end'] <= friends[name]['end'],
            meeting_vars[name]['end'] - meeting_vars[name]['start'] >= friends[name]['min_duration']
        )))
        s.add(Implies(Not(met[name]), And(
            meeting_vars[name]['start'] == 0,
            meeting_vars[name]['end'] == 0
        )))

    # Ordering constraints between meetings to ensure travel times are respected
    # We'll need to define an order in which meetings occur. This is complex, so we'll
    # use a simple approach: choose an order and enforce travel times between consecutive meetings.

    # Since the problem is complex, we'll assume a certain order and let the solver find a feasible schedule.
    # Alternatively, we can iterate over possible orders, but that's computationally expensive.

    # For simplicity, we'll prioritize meeting friends with tighter time windows first.

    # Let's try to meet Jason first (since his window is early and tight)
    # Then Mark, Kenneth, Kimberly, Stephanie, Jessica, Brian, Steven, Karen.

    # Define the order based on start times
    ordered_friends = sorted(friends.keys(), key=lambda x: friends[x]['start'])

    # Add constraints for travel times between consecutive meetings
    for i in range(len(ordered_friends) - 1):
        name1 = ordered_friends[i]
        name2 = ordered_friends[i + 1]
        loc1 = friends[name1]['location']
        loc2 = friends[name2]['location']
        travel_time = travel_times.get((loc1, loc2), 0)
        s.add(Implies(And(met[name1], met[name2]),
              meeting_vars[name2]['start'] >= meeting_vars[name1]['end'] + travel_time)

    # Maximize the number of friends met
    s.maximize(Sum([If(met[name], 1, 0) for name in friends]))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for name in friends:
            if model.evaluate(met[name]):
                start = model.evaluate(meeting_vars[name]['start']).as_long()
                end = model.evaluate(meeting_vars[name]['end']).as_long()
                # Convert minutes to HH:MM format
                start_hour = (start // 60) % 24
                start_min = start % 60
                end_hour = (end // 60) % 24
                end_min = end % 60
                start_time = f"{start_hour:02d}:{start_min:02d}"
                end_time = f"{end_hour:02d}:{end_min:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_time,
                    "end_time": end_time
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x['start_time'])
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Run the solver and print the result
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))