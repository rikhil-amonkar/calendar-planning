from z3 import *
import json

def solve_scheduling_problem():
    # Initialize solver with optimization
    opt = Optimize()

    # Define friends and their details
    friends = {
        "Paul": {"location": "Nob Hill", "available_start": 16*60 + 15, "available_end": 21*60 + 15, "min_duration": 60},
        "Carol": {"location": "Union Square", "available_start": 18*60, "available_end": 20*60 + 15, "min_duration": 120},
        "Patricia": {"location": "Chinatown", "available_start": 20*60, "available_end": 21*60 + 30, "min_duration": 75},
        "Karen": {"location": "The Castro", "available_start": 17*60, "available_end": 19*60, "min_duration": 45},
        "Nancy": {"location": "Presidio", "available_start": 11*60 + 45, "available_end": 22*60, "min_duration": 30},
        "Jeffrey": {"location": "Pacific Heights", "available_start": 20*60, "available_end": 20*60 + 45, "min_duration": 45},
        "Matthew": {"location": "Russian Hill", "available_start": 15*60 + 45, "available_end": 21*60 + 45, "min_duration": 75}
    }

    # Travel times between locations
    travel_times = {
        "Bayview": {"Nob Hill": 20, "Union Square": 17, "Chinatown": 18, "The Castro": 20, "Presidio": 31, "Pacific Heights": 23, "Russian Hill": 23},
        "Nob Hill": {"Bayview": 19, "Union Square": 7, "Chinatown": 6, "The Castro": 17, "Presidio": 17, "Pacific Heights": 8, "Russian Hill": 5},
        "Union Square": {"Bayview": 15, "Nob Hill": 9, "Chinatown": 7, "The Castro": 19, "Presidio": 24, "Pacific Heights": 15, "Russian Hill": 13},
        "Chinatown": {"Bayview": 22, "Nob Hill": 8, "Union Square": 7, "The Castro": 22, "Presidio": 19, "Pacific Heights": 10, "Russian Hill": 7},
        "The Castro": {"Bayview": 19, "Nob Hill": 16, "Union Square": 19, "Chinatown": 20, "Presidio": 20, "Pacific Heights": 16, "Russian Hill": 18},
        "Presidio": {"Bayview": 31, "Nob Hill": 18, "Union Square": 22, "Chinatown": 21, "The Castro": 21, "Pacific Heights": 11, "Russian Hill": 14},
        "Pacific Heights": {"Bayview": 22, "Nob Hill": 8, "Union Square": 12, "Chinatown": 11, "The Castro": 16, "Presidio": 11, "Russian Hill": 7},
        "Russian Hill": {"Bayview": 23, "Nob Hill": 5, "Union Square": 11, "Chinatown": 9, "The Castro": 21, "Presidio": 14, "Pacific Heights": 7}
    }

    # Create variables and basic constraints
    variables = {}
    scheduled = {}  # Whether each friend is scheduled
    for name in friends:
        start_var = Int(f'start_{name}')
        end_var = Int(f'end_{name}')
        scheduled_var = Bool(f'scheduled_{name}')
        variables[name] = {'start': start_var, 'end': end_var, 'scheduled': scheduled_var}
        
        friend = friends[name]
        opt.add(Implies(scheduled_var, start_var >= friend['available_start']))
        opt.add(Implies(scheduled_var, end_var <= friend['available_end']))
        opt.add(Implies(scheduled_var, end_var - start_var >= friend['min_duration']))

    # Define order variables
    order = {name: Int(f'order_{name}') for name in friends}
    opt.add(Distinct([order[name] for name in friends]))
    for name in friends:
        opt.add(Implies(variables[name]['scheduled'], order[name] >= 1))
        opt.add(Implies(variables[name]['scheduled'], order[name] <= len(friends)))
        opt.add(Implies(Not(variables[name]['scheduled']), order[name] == 0))

    # Starting point
    current_time = 540  # 9:00 AM
    current_location = "Bayview"

    # First meeting constraints
    for name in friends:
        loc = friends[name]['location']
        travel_time = travel_times[current_location][loc]
        opt.add(Implies(And(variables[name]['scheduled'], order[name] == 1), 
                       variables[name]['start'] >= current_time + travel_time))

    # Sequence constraints
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                loc1 = friends[name1]['location']
                loc2 = friends[name2]['location']
                travel_time = travel_times[loc1][loc2]
                opt.add(Implies(And(variables[name1]['scheduled'], variables[name2]['scheduled'],
                                order[name1] < order[name2]), 
                        variables[name2]['start'] >= variables[name1]['end'] + travel_time))

    # Optimization objective: maximize number of scheduled meetings
    opt.maximize(Sum([If(variables[name]['scheduled'], 1, 0) for name in friends]))

    # Try to solve
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        meetings = []
        
        for name in friends:
            if is_true(model.evaluate(variables[name]['scheduled'])):
                start_val = model.evaluate(variables[name]['start']).as_long()
                end_val = model.evaluate(variables[name]['end']).as_long()
                order_val = model.evaluate(order[name]).as_long()
                meetings.append((order_val, name, start_val, end_val))
        
        meetings.sort()
        
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

solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))