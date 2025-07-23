from z3 import *

def main():
    # Define friends: (name, location, window_start, window_end, min_duration)
    friends = [
        ('Mary', 'Golden Gate Park', -15, 165, 45),
        ('Kevin', 'Haight-Ashbury', 75, 435, 90),
        ('Deborah', 'Bayview', 360, 615, 120),
        ('Stephanie', 'Presidio', 60, 495, 120),
        ('Emily', 'Financial District', 150, 765, 105)
    ]
    friend_names = [f[0] for f in friends]
    
    # Travel data: (from, to, minutes)
    travel_tuples = [
        ("Embarcadero", "Golden Gate Park", 25),
        ("Embarcadero", "Haight-Ashbury", 21),
        ("Embarcadero", "Bayview", 21),
        ("Embarcadero", "Presidio", 20),
        ("Embarcadero", "Financial District", 5),
        ("Golden Gate Park", "Embarcadero", 25),
        ("Golden Gate Park", "Haight-Ashbury", 7),
        ("Golden Gate Park", "Bayview", 23),
        ("Golden Gate Park", "Presidio", 11),
        ("Golden Gate Park", "Financial District", 26),
        ("Haight-Ashbury", "Embarcadero", 20),
        ("Haight-Ashbury", "Golden Gate Park", 7),
        ("Haight-Ashbury", "Bayview", 18),
        ("Haight-Ashbury", "Presidio", 15),
        ("Haight-Ashbury", "Financial District", 21),
        ("Bayview", "Embarcadero", 19),
        ("Bayview", "Golden Gate Park", 22),
        ("Bayview", "Haight-Ashbury", 19),
        ("Bayview", "Presidio", 31),
        ("Bayview", "Financial District", 19),
        ("Presidio", "Embarcadero", 20),
        ("Presidio", "Golden Gate Park", 12),
        ("Presidio", "Haight-Ashbury", 15),
        ("Presidio", "Bayview", 31),
        ("Presidio", "Financial District", 23),
        ("Financial District", "Embarcadero", 4),
        ("Financial District", "Golden Gate Park", 23),
        ("Financial District", "Haight-Ashbury", 19),
        ("Financial District", "Bayview", 19),
        ("Financial District", "Presidio", 22)
    ]
    
    # Build travel_dict: travel_dict[from][to] = time
    travel_dict = {}
    locations = set()
    for t in travel_tuples:
        from_loc, to_loc, time = t
        locations.add(from_loc)
        locations.add(to_loc)
    for loc in locations:
        travel_dict[loc] = {}
    for t in travel_tuples:
        from_loc, to_loc, time = t
        travel_dict[from_loc][to_loc] = time

    # Mapping from friend name to location
    loc_dict = {}
    for name, loc, win_start, win_end, dur_min in friends:
        loc_dict[name] = loc

    # Create Z3 variables
    s = {}
    meet = {}
    pos_val = {}
    for name, loc, win_start, win_end, dur_min in friends:
        s[name] = Int(f's_{name}')
        meet[name] = Bool(f'meet_{name}')
        pos_val[name] = Int(f'pos_{name}')
    
    solver = Optimize()
    
    # Constraints for meeting windows and durations
    for name, loc, win_start, win_end, dur_min in friends:
        solver.add(Implies(meet[name], s[name] >= win_start))
        solver.add(Implies(meet[name], s[name] + dur_min <= win_end))
    
    # Position constraints: distinct positions for scheduled meetings, and in [0,4]
    for name in friend_names:
        solver.add(Implies(meet[name], And(pos_val[name] >= 0, pos_val[name] < 5)))
    for i in range(len(friend_names)):
        for j in range(i+1, len(friend_names)):
            n1 = friend_names[i]
            n2 = friend_names[j]
            solver.add(Implies(And(meet[n1], meet[n2]), pos_val[n1] != pos_val[n2]))
    
    # Constraint: if a position p (>=1) is used, then position p-1 must be used
    for p in range(1,5):
        exists_p = Or([And(meet[name], pos_val[name] == p) for name in friend_names])
        exists_p_minus_1 = Or([And(meet[name], pos_val[name] == p-1) for name in friend_names])
        solver.add(Implies(exists_p, exists_p_minus_1))
    
    # Travel constraints: first meeting
    for name, loc, win_start, win_end, dur_min in friends:
        from_loc = "Embarcadero"
        to_loc = loc_dict[name]
        t_time = travel_dict[from_loc][to_loc]
        solver.add(Implies(And(meet[name], pos_val[name] == 0), s[name] >= t_time))
    
    # Travel constraints: consecutive meetings
    for i in range(len(friend_names)):
        name_i = friend_names[i]
        loc_i = loc_dict[name_i]
        dur_i = friends[i][4]
        for j in range(len(friend_names)):
            if i == j:
                continue
            name_j = friend_names[j]
            loc_j = loc_dict[name_j]
            t_time = travel_dict[loc_i][loc_j]
            solver.add(Implies(
                And(meet[name_i], meet[name_j], pos_val[name_j] == pos_val[name_i] + 1),
                s[name_j] >= s[name_i] + dur_i + t_time
            ))
    
    # Objective: maximize the number of meetings
    total_meetings = Sum([If(meet[name], 1, 0) for name in friend_names])
    solver.maximize(total_meetings)
    
    # Solve
    if solver.check() == sat:
        model = solver.model()
        scheduled_meetings = []
        for name in friend_names:
            if is_true(model[meet[name]]):
                start_val = model[s[name]].as_long()
                pos_int = model[pos_val[name]].as_long()
                dur_min = next(f[4] for f in friends if f[0] == name)
                end_val = start_val + dur_min
                # Convert start_val and end_val to time strings
                hour_start = 9 + start_val // 60
                minute_start = start_val % 60
                start_time_str = f"{hour_start:02d}:{minute_start:02d}"
                hour_end = 9 + end_val // 60
                minute_end = end_val % 60
                end_time_str = f"{hour_end:02d}:{minute_end:02d}"
                scheduled_meetings.append((pos_int, name, start_time_str, end_time_str))
        
        # Sort by position
        scheduled_meetings.sort(key=lambda x: x[0])
        itinerary = []
        for pos, name, start_str, end_str in scheduled_meetings:
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print("SOLUTION:")
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()