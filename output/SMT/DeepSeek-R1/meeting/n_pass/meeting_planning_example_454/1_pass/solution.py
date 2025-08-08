from z3 import *

def main():
    # Travel time matrix: 0:Presidio, 1:Golden Gate Park, 2:Bayview, 3:Chinatown, 4:North Beach, 5:Mission District
    T = [
        [0, 12, 31, 21, 18, 26],
        [11, 0, 23, 23, 24, 17],
        [31, 22, 0, 18, 21, 13],
        [19, 23, 22, 0, 3, 18],
        [17, 22, 22, 6, 0, 18],
        [25, 17, 15, 16, 17, 0]
    ]
    
    # Friends data: (name, location_index, min_duration, available_start (min), available_end (min))
    friends = {
        1: ("Jessica", 1, 30, 825, 900),      # Golden Gate Park
        2: ("Ashley", 2, 105, 1035, 1200),     # Bayview
        3: ("Ronald", 3, 90, 435, 885),        # Chinatown
        4: ("William", 4, 15, 795, 1215),      # North Beach
        5: ("Daniel", 5, 105, 420, 675)        # Mission District
    }
    
    # Create Z3 variables
    meet_vars = []
    s_vars = []
    e_vars = []
    for i in range(1, 6):
        meet_vars.append(Bool(f'meet{i}'))
        s_vars.append(Int(f's{i}'))
        e_vars.append(Int(f'e{i}'))
    
    # Start at Presidio (dummy meeting0)
    s0 = 540
    e0 = 540
    
    # Use Optimize for maximization
    opt = Optimize()
    
    # Add constraints for each friend
    for idx, (name, loc, dur, avail_start, avail_end) in friends.items():
        i = idx - 1  # index in meet_vars, s_vars, e_vars
        # If meeting this friend, set end time and availability constraints
        opt.add(Implies(meet_vars[i], e_vars[i] == s_vars[i] + dur))
        opt.add(Implies(meet_vars[i], s_vars[i] >= avail_start))
        opt.add(Implies(meet_vars[i], s_vars[i] <= avail_end - dur))
        # Set bounds to help solver
        opt.add(Implies(meet_vars[i], s_vars[i] >= 0))
        opt.add(Implies(meet_vars[i], s_vars[i] <= 1440))  # 24*60
    
    # Create lists including the dummy meeting0
    all_meet = [True] + meet_vars
    all_s = [s0] + s_vars
    all_e = [e0] + e_vars
    
    # Add disjunctive constraints for every pair of meetings (including dummy)
    n = 6  # 0 to 5
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            # Condition: either j starts after i ends plus travel, or vice versa
            cond = Or(
                all_s[j] >= all_e[i] + T[i][j],
                all_s[i] >= all_e[j] + T[j][i]
            )
            # If both meetings are active, enforce the condition
            opt.add(Implies(And(all_meet[i], all_meet[j]), cond))
    
    # Maximize the number of friends met
    count = Sum([If(meet_vars[i], 1, 0) for i in range(5)])
    opt.maximize(count)
    
    # Check and get model
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        for idx in range(1, 6):
            if is_true(model.eval(meet_vars[idx-1])):
                name, loc, dur, avail_start, avail_end = friends[idx]
                s_val = model.eval(s_vars[idx-1]).as_long()
                e_val = model.eval(e_vars[idx-1]).as_long()
                # Convert minutes to HH:MM
                start_h = s_val // 60
                start_m = s_val % 60
                end_h = e_val // 60
                end_m = e_val % 60
                start_str = f"{start_h:02d}:{start_m:02d}"
                end_str = f"{end_h:02d}:{end_m:02d}"
                itinerary.append({
                    "action": "meet",
                    "person": name,
                    "start_time": start_str,
                    "end_time": end_str
                })
        # Sort itinerary by start time
        itinerary.sort(key=lambda x: x["start_time"])
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()