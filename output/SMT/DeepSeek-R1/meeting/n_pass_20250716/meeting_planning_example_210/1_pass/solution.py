from z3 import *

def main():
    # Define travel times between locations
    travel_times = {
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Financial District'): 23,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Financial District'): 22,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Richmond District'): 21
    }
    
    # Map friends to their locations
    loc_map = {
        'Emily': 'Presidio',
        'Joseph': 'Richmond District',
        'Melissa': 'Financial District'
    }
    
    friends = ['Emily', 'Joseph', 'Melissa']
    
    # Initialize the optimization solver
    opt = Optimize()
    
    # Create variables for each friend: whether met, start time, and duration
    met = {f: Bool(f'met_{f}') for f in friends}
    start = {f: Int(f'start_{f}') for f in friends}
    dur = {f: Int(f'dur_{f}') for f in friends}
    
    # Define order variables for pairs (i < j)
    pairs = [('Emily', 'Joseph'), ('Emily', 'Melissa'), ('Joseph', 'Melissa')]
    before = {(i, j): Bool(f'before_{i}_{j}') for (i, j) in pairs}
    
    # Add constraints for each friend
    for f in friends:
        loc_f = loc_map[f]
        travel_from_fisher = travel_times[('Fisherman\'s Wharf', loc_f)]
        if f == 'Emily':
            min_start = 435  # 4:15 PM
            max_end = 720    # 9:00 PM
            min_dur = 105
        elif f == 'Joseph':
            min_start = 495  # 5:15 PM
            max_end = 780    # 10:00 PM
            min_dur = 120
        else:  # Melissa
            min_start = 405  # 3:45 PM
            max_end = 765    # 9:45 PM
            min_dur = 75
        
        # If meeting the friend, enforce constraints
        opt.add(Implies(met[f], 
                       And(start[f] >= travel_from_fisher,
                           start[f] >= min_start,
                           start[f] + dur[f] <= max_end,
                           dur[f] >= min_dur)))
    
    # Add constraints for each pair of friends
    for (i, j) in pairs:
        loc_i = loc_map[i]
        loc_j = loc_map[j]
        travel_ij = travel_times[(loc_i, loc_j)]
        travel_ji = travel_times[(loc_j, loc_i)]
        bij = before[(i, j)]
        opt.add(Implies(And(met[i], met[j]),
                       Or(And(bij, start[j] >= start[i] + dur[i] + travel_ij),
                          And(Not(bij), start[i] >= start[j] + dur[j] + travel_ji))))
    
    # Maximize the number of friends met
    total_met = Sum([If(met[f], 1, 0) for f in friends])
    opt.maximize(total_met)
    
    # Check for a solution and print results
    if opt.check() == sat:
        m = opt.model()
        total_met_val = m.evaluate(total_met).as_long()
        print(f"Total meetings: {total_met_val}")
        for f in friends:
            if m.evaluate(met[f]):
                s_val = m.evaluate(start[f]).as_long()
                d_val = m.evaluate(dur[f]).as_long()
                total_minutes = s_val
                hours_from_9 = total_minutes // 60
                minutes_val = total_minutes % 60
                total_hours = 9 + hours_from_9
                hour_val = total_hours % 12
                if hour_val == 0:
                    hour_val = 12
                period = "AM" if total_hours < 12 else "PM"
                time_str = f"{hour_val}:{minutes_val:02d} {period}"
                print(f"Meet {f} at {loc_map[f]} starting at {time_str} for {d_val} minutes")
            else:
                print(f"Do not meet {f}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()