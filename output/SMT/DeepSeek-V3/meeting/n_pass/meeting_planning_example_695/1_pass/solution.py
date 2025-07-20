from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their details
    friends = {
        "Paul": {"location": "Nob Hill", "available_start": 16*60 + 15, "available_end": 21*60 + 15, "min_duration": 60},
        "Carol": {"location": "Union Square", "available_start": 18*60, "available_end": 20*60 + 15, "min_duration": 120},
        "Patricia": {"location": "Chinatown", "available_start": 20*60, "available_end": 21*60 + 30, "min_duration": 75},
        "Karen": {"location": "The Castro", "available_start": 17*60, "available_end": 19*60, "min_duration": 45},
        "Nancy": {"location": "Presidio", "available_start": 11*60 + 45, "available_end": 22*60, "min_duration": 30},
        "Jeffrey": {"location": "Pacific Heights", "available_start": 20*60, "available_end": 20*60 + 45, "min_duration": 45},
        "Matthew": {"location": "Russian Hill", "available_start": 15*60 + 45, "available_end": 21*60 + 45, "min_duration": 75}
    }

    # Define travel times between locations (in minutes)
    travel_times = {
        "Bayview": {
            "Nob Hill": 20,
            "Union Square": 17,
            "Chinatown": 18,
            "The Castro": 20,
            "Presidio": 31,
            "Pacific Heights": 23,
            "Russian Hill": 23
        },
        "Nob Hill": {
            "Bayview": 19,
            "Union Square": 7,
            "Chinatown": 6,
            "The Castro": 17,
            "Presidio": 17,
            "Pacific Heights": 8,
            "Russian Hill": 5
        },
        "Union Square": {
            "Bayview": 15,
            "Nob Hill": 9,
            "Chinatown": 7,
            "The Castro": 19,
            "Presidio": 24,
            "Pacific Heights": 15,
            "Russian Hill": 13
        },
        "Chinatown": {
            "Bayview": 22,
            "Nob Hill": 8,
            "Union Square": 7,
            "The Castro": 22,
            "Presidio": 19,
            "Pacific Heights": 10,
            "Russian Hill": 7
        },
        "The Castro": {
            "Bayview": 19,
            "Nob Hill": 16,
            "Union Square": 19,
            "Chinatown": 20,
            "Presidio": 20,
            "Pacific Heights": 16,
            "Russian Hill": 18
        },
        "Presidio": {
            "Bayview": 31,
            "Nob Hill": 18,
            "Union Square": 22,
            "Chinatown": 21,
            "The Castro": 21,
            "Pacific Heights": 11,
            "Russian Hill": 14
        },
        "Pacific Heights": {
            "Bayview": 22,
            "Nob Hill": 8,
            "Union Square": 12,
            "Chinatown": 11,
            "The Castro": 16,
            "Presidio": 11,
            "Russian Hill": 7
        },
        "Russian Hill": {
            "Bayview": 23,
            "Nob Hill": 5,
            "Union Square": 11,
            "Chinatown": 9,
            "The Castro": 21,
            "Presidio": 14,
            "Pacific Heights": 7
        }
    }

    # Create variables for each friend's meeting start and end times
    variables = {}
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        variables[name] = {'start': start_var, 'end': end_var}

    # Constraints for each friend's meeting
    for name in friends:
        friend = friends[name]
        start = variables[name]['start']
        end = variables[name]['end']
        s.add(start >= friend['available_start'])
        s.add(end <= friend['available_end'])
        s.add(end - start >= friend['min_duration'])

    # Initial location is Bayview at 9:00 AM (540 minutes)
    current_time = 540  # 9:00 AM in minutes
    current_location = "Bayview"

    # We need to sequence the meetings considering travel times
    # This is a complex part; we'll need to model the order of meetings
    # For simplicity, let's assume we can meet friends in any order, but travel times must be respected

    # To model the order, we can use a list of booleans indicating whether a meeting is scheduled before another
    # However, this is complex. Alternatively, we can try to find a feasible order by trying permutations
    # But with 7 friends, that's 7! = 5040 permutations, which is manageable for Z3 with some constraints

    # Instead, let's define an order variable for each friend
    order = {name: Int(f'order_{name}') for name in friends}
    s.add(Distinct([order[name] for name in friends]))
    for name in friends:
        s.add(order[name] >= 1)
        s.add(order[name] <= len(friends))

    # Now, for each pair of friends, if order[A] < order[B], then start_B >= end_A + travel_time(A.loc to B.loc)
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                loc1 = friends[name1]['location']
                loc2 = friends[name2]['location']
                travel_time = travel_times[loc1][loc2]
                s.add(Implies(order[name1] < order[name2], 
                              variables[name2]['start'] >= variables[name1]['end'] + travel_time))

    # Also, the first meeting must start after current_time + travel from current_location to the first friend's location
    for name in friends:
        loc = friends[name]['location']
        travel_time = travel_times[current_location][loc]
        s.add(Implies(order[name] == 1, variables[name]['start'] >= current_time + travel_time))

    # To maximize the number of friends met, we can use a soft constraint or optimize
    # Here, we'll just check for a feasible solution that meets all constraints
    # To prioritize certain friends, we can adjust the constraints or order

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        # Collect all meetings with their start and end times
        meetings = []
        for name in friends:
            start_val = model.evaluate(variables[name]['start']).as_long()
            end_val = model.evaluate(variables[name]['end']).as_long()
            order_val = model.evaluate(order[name]).as_long()
            meetings.append((order_val, name, start_val, end_val))
        
        # Sort meetings by order
        meetings.sort()
        
        # Convert to itinerary format
        for _, name, start_val, end_val in meetings:
            start_hour = start_val // 60
            start_min = start_val % 60
            end_hour = end_val // 60
            end_min = end_val % 60
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": f"{start_hour:02d}:{start_min:02d}",
                "end_time": f"{end_hour:02d}:{end_min:02d}"
            })
        
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve the problem and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))