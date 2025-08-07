import json
from z3 import *

def main():
    # Travel times dictionary: from_location -> to_location -> minutes
    travel_dict = {
        'B': {'R': 23, 'A': 16, 'N': 21, 'F': 19},
        'R': {'B': 23, 'A': 15, 'N': 5, 'F': 11},
        'A': {'B': 16, 'R': 13, 'N': 15, 'F': 17},
        'N': {'B': 22, 'R': 4, 'A': 16, 'F': 8},
        'F': {'B': 19, 'R': 10, 'A': 17, 'N': 7}
    }
    
    # Friend details: name, location, start_min (window start in minutes from midnight), 
    # end_max (window end in minutes from midnight), duration (minimum meeting duration in minutes)
    friends = [
        {"name": "Joseph", "loc": "R", "start_min": 510, "end_max": 1155, "duration": 60},
        {"name": "Nancy", "loc": "A", "start_min": 660, "end_max": 960, "duration": 90},
        {"name": "Jason", "loc": "N", "start_min": 1005, "end_max": 1305, "duration": 15},
        {"name": "Jeffrey", "loc": "F", "start_min": 630, "end_max": 945, "duration": 45}
    ]
    
    # Create Z3 variables for each friend: a boolean for whether we meet and an integer for start time
    for friend in friends:
        friend['meet_var'] = Bool(f"meet_{friend['name']}")
        friend['start_var'] = Int(f"start_{friend['name']}")
    
    s = Solver()
    
    # Add individual constraints for each friend
    for friend in friends:
        meet_var = friend['meet_var']
        start_var = friend['start_var']
        loc = friend['loc']
        travel_time_from_start = travel_dict['B'][loc]
        min_start = max(friend['start_min'], 540 + travel_time_from_start)
        # Start time must be at least min_start and the meeting must end by end_max
        s.add(Implies(meet_var, start_var >= min_start))
        s.add(Implies(meet_var, start_var + friend['duration'] <= friend['end_max']))
        # Also, the start time must be non-negative
        s.add(Implies(meet_var, start_var >= 0))
    
    # Create before variables for every ordered pair (i, j) with i != j
    before_vars = {}
    n = len(friends)
    for i in range(n):
        for j in range(n):
            if i != j:
                before_vars[(i, j)] = Bool(f"before_{i}_{j}")
    
    # Add pairwise disjunctive constraints
    for i in range(n):
        for j in range(n):
            if i != j:
                friend_i = friends[i]
                friend_j = friends[j]
                meet_i = friend_i['meet_var']
                meet_j = friend_j['meet_var']
                start_i = friend_i['start_var']
                start_j = friend_j['start_var']
                dur_i = friend_i['duration']
                dur_j = friend_j['duration']
                loc_i = friend_i['loc']
                loc_j = friend_j['loc']
                travel_ij = travel_dict[loc_i][loc_j]
                travel_ji = travel_dict[loc_j][loc_i]
                
                # If both meetings happen, then either i before j or j before i
                constraint = Or(
                    And(before_vars[(i, j)], start_i + dur_i + travel_ij <= start_j),
                    And(Not(before_vars[(i, j)]), start_j + dur_j + travel_ji <= start_i)
                )
                s.add(Implies(And(meet_i, meet_j), constraint))
    
    # Add transitivity constraints for every distinct triplet (i, j, k)
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            for k in range(n):
                if i == k or j == k:
                    continue
                s.add(Implies(
                    And(friends[i]['meet_var'], friends[j]['meet_var'], friends[k]['meet_var']),
                    Implies(
                        And(before_vars[(i, j)], before_vars[(j, k)]),
                        before_vars[(i, k)]
                    )
                ))
    
    # Maximize the number of friends met
    opt = Optimize()
    opt.add(s.assertions())
    total_meet = Sum([If(f['meet_var'], 1, 0) for f in friends])
    opt.maximize(total_meet)
    
    itinerary = []
    if opt.check() == sat:
        model = opt.model()
        for friend in friends:
            if model.eval(friend['meet_var']):
                start_val = model.eval(friend['start_var']).as_long()
                end_val = start_val + friend['duration']
                start_hour = start_val // 60
                start_minute = start_val % 60
                end_hour = end_val // 60
                end_minute = end_val % 60
                start_str = f"{start_hour:02d}:{start_minute:02d}"
                end_str = f"{end_hour:02d}:{end_minute:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": friend['name'],
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort itinerary by start_time
        itinerary.sort(key=lambda x: x['start_time'])
    
    # Output the itinerary in JSON format
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()