from z3 import *
import json
from itertools import permutations

def solve_scheduling_problem():
    s = Optimize()

    # Define friends and their availability
    friends = {
        "Elizabeth": {"location": "Financial District", "start": "10:00", "end": "12:45", "min_duration": 75},
        "Joseph": {"location": "Union Square", "start": "11:45", "end": "14:45", "min_duration": 120},
        "Ashley": {"location": "Russian Hill", "start": "11:30", "end": "21:30", "min_duration": 45},
        "Karen": {"location": "Mission District", "start": "14:15", "end": "22:00", "min_duration": 30},
        "Richard": {"location": "Fisherman's Wharf", "start": "14:30", "end": "17:30", "min_duration": 30},
        "Kimberly": {"location": "Haight-Ashbury", "start": "14:15", "end": "17:30", "min_duration": 105},
        "Helen": {"location": "Sunset District", "start": "14:45", "end": "20:45", "min_duration": 105},
        "Robert": {"location": "Presidio", "start": "21:45", "end": "22:45", "min_duration": 60}
    }

    # Convert time to minutes since 9:00 AM (540 minutes since midnight)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540

    def minutes_to_time(minutes):
        total = minutes + 540
        hh = total // 60
        mm = total % 60
        return f"{hh:02d}:{mm:02d}"

    # Create variables for each meeting
    variables = {}
    for name in friends:
        variables[name] = {
            'start': Int(f'start_{name}'),
            'end': Int(f'end_{name}'),
            'met': Bool(f'met_{name}')  # Whether we meet this friend
        }

    # Travel times between locations
    travel_times = {
        ("Financial District", "Union Square"): 9,
        ("Union Square", "Russian Hill"): 13,
        ("Russian Hill", "Mission District"): 16,
        ("Mission District", "Fisherman's Wharf"): 22,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Sunset District", "Presidio"): 16,
        ("Financial District", "Russian Hill"): 11,
        ("Russian Hill", "Union Square"): 10,
        ("Mission District", "Haight-Ashbury"): 12,
        ("Haight-Ashbury", "Mission District"): 11,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Presidio", "Sunset District"): 15,
        ("Marina District", "Financial District"): 17,
        ("Financial District", "Marina District"): 15,
        ("Marina District", "Union Square"): 16,
        ("Union Square", "Marina District"): 18,
        ("Marina District", "Russian Hill"): 8,
        ("Russian Hill", "Marina District"): 7,
        ("Marina District", "Mission District"): 20,
        ("Mission District", "Marina District"): 19,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Marina District", "Presidio"): 10,
        ("Presidio", "Marina District"): 11,
        ("Marina District", "Sunset District"): 19,
        ("Sunset District", "Marina District"): 21,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Haight-Ashbury", "Marina District"): 17
    }

    # Base constraints for each friend
    for name in friends:
        friend = friends[name]
        start_time = time_to_minutes(friend['start'])
        end_time = time_to_minutes(friend['end'])
        min_duration = friend['min_duration']

        # If we meet this friend, enforce time constraints
        s.add(Implies(variables[name]['met'],
                      And(variables[name]['start'] >= start_time,
                          variables[name]['end'] <= end_time,
                          variables[name]['end'] - variables[name]['start'] >= min_duration)))

    # Meeting sequence constraints
    # We'll try to meet as many friends as possible
    num_met = Int('num_met')
    s.add(num_met == Sum([If(variables[name]['met'], 1, 0) for name in friends]))
    s.maximize(num_met)

    # Create ordering variables to sequence the meetings
    order = {name: Int(f'order_{name}') for name in friends}
    for name in friends:
        s.add(Implies(variables[name]['met'], And(order[name] >= 1, order[name] <= len(friends))))

    # All met friends have unique order numbers
    s.add(Distinct([If(variables[name]['met'], order[name], 0) for name in friends]))

    # Travel time constraints between consecutive meetings
    for name1 in friends:
        for name2 in friends:
            if name1 != name2:
                loc1 = friends[name1]['location']
                loc2 = friends[name2]['location']
                travel = travel_times.get((loc1, loc2), 60)  # Default to 60 if not found
                
                s.add(Implies(And(variables[name1]['met'], variables[name2]['met'], 
                                order[name2] == order[name1] + 1),
                            variables[name2]['start'] >= variables[name1]['end'] + travel))

    # Ensure first meeting starts after 9:00 AM
    s.add(Or([And(variables[name]['met'], variables[name]['start'] >= 0) for name in friends]))

    # Try to solve
    if s.check() == sat:
        m = s.model()
        itinerary = []
        # Get all met friends and their order
        met_friends = [(name, m.evaluate(order[name]).as_long()) 
                      for name in friends if is_true(m.evaluate(variables[name]['met']))]
        # Sort by order
        met_friends.sort(key=lambda x: x[1])
        
        for name, _ in met_friends:
            start = m.evaluate(variables[name]['start']).as_long()
            end = m.evaluate(variables[name]['end']).as_long()
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(end)
            })
        return {"itinerary": itinerary}
    else:
        return {"itinerary": []}

# Solve and print the solution
solution = solve_scheduling_problem()
print(json.dumps(solution, indent=2))