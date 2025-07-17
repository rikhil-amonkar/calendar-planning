from z3 import *

def main():
    opt = Optimize()
    
    # Meet variables for each friend: Mary (0), Kevin (1), Deborah (2), Stephanie (3), Emily (4)
    meet = [Bool(f"meet_{i}") for i in range(5)]
    
    # Arrival time variables for each friend (in minutes from 9:00 AM)
    T = [Real(f"T_{i}") for i in range(5)]
    
    # Edge variables: 7x7 matrix (nodes: 0,1,2,3,4,5,6) 
    # where 5 = Start (Embarcadero), 6 = End (dummy node)
    x = [[Bool(f"x_{i}_{j}") for j in range(7)] for i in range(7)]
    
    # Disallow invalid edges
    for i in range(7):
        for j in range(7):
            # No self edges
            if i == j:
                opt.add(x[i][j] == False)
            # End node (6) has no outgoing edges
            if i == 6:
                opt.add(x[i][j] == False)
            # Friends (0-4) cannot go to Start (5)
            if i in [0, 1, 2, 3, 4] and j == 5:
                opt.add(x[i][j] == False)
            # Start (5) cannot go to itself or End (6)
            if i == 5 and j in [5, 6]:
                opt.add(x[i][j] == False)
    
    # Flow constraints
    # Start (5) must have one outgoing edge to a friend
    opt.add(Sum([x[5][j] for j in range(5)]) == 1)
    
    # For each friend, incoming and outgoing edges must match meet_i
    for i in range(5):
        # Incoming edges: from Start (5) or other friends (0-4) but not self
        in_edges = [x[k][i] for k in [5] + list(range(5)) if k != i]
        opt.add(Sum(in_edges) == If(meet[i], 1, 0))
        
        # Outgoing edges: to other friends (0-4) or End (6) but not self
        out_edges = [x[i][j] for j in list(range(5)) + [6] if j != i]
        opt.add(Sum(out_edges) == If(meet[i], 1, 0))
    
    # End (6) must have one incoming edge from a friend
    opt.add(Sum([x[i][6] for i in range(5)]) == 1)
    
    # Travel time matrix (in minutes)
    travel_time = [[0] * 7 for _ in range(7)]
    
    # Start (5) to friends
    travel_time[5][0] = 25  # to Mary (Golden Gate Park)
    travel_time[5][1] = 21  # to Kevin (Haight-Ashbury)
    travel_time[5][2] = 21  # to Deborah (Bayview)
    travel_time[5][3] = 20  # to Stephanie (Presidio)
    travel_time[5][4] = 5   # to Emily (Financial District)
    
    # Mary (0) to others
    travel_time[0][1] = 7   # to Kevin
    travel_time[0][2] = 23  # to Deborah
    travel_time[0][3] = 11  # to Stephanie
    travel_time[0][4] = 26  # to Emily
    
    # Kevin (1) to others
    travel_time[1][0] = 7   # to Mary
    travel_time[1][2] = 18  # to Deborah
    travel_time[1][3] = 15  # to Stephanie
    travel_time[1][4] = 21  # to Emily
    
    # Deborah (2) to others
    travel_time[2][0] = 22  # to Mary
    travel_time[2][1] = 19  # to Kevin
    travel_time[2][3] = 31  # to Stephanie
    travel_time[2][4] = 19  # to Emily
    
    # Stephanie (3) to others
    travel_time[3][0] = 12  # to Mary
    travel_time[3][1] = 15  # to Kevin
    travel_time[3][2] = 31  # to Deborah
    travel_time[3][4] = 23  # to Emily
    
    # Emily (4) to others
    travel_time[4][0] = 23  # to Mary
    travel_time[4][1] = 19  # to Kevin
    travel_time[4][2] = 19  # to Deborah
    travel_time[4][3] = 22  # to Stephanie
    
    # Minimum meeting durations (in minutes)
    min_duration = [45, 90, 120, 120, 105]  # Mary, Kevin, Deborah, Stephanie, Emily
    
    # Availability windows (in minutes from 9:00 AM)
    window_start = [-15, 75, 360, 60, 150]  # Mary, Kevin, Deborah, Stephanie, Emily
    window_end = [165, 435, 615, 495, 765]   # Mary, Kevin, Deborah, Stephanie, Emily
    
    # Time constraints for each friend
    for i in range(5):
        # Predecessor constraints: if met and edge from k to i, then T_i >= (T_k + min_duration_k) + travel_time[k][i] (or 0 if k is Start)
        for k in [5] + list(range(5)):
            if k == i:
                continue
            if k == 5:
                base = 0
            else:
                base = T[k] + min_duration[k]
            opt.add(Implies(And(meet[i], x[k][i]), T[i] >= base + travel_time[k][i]))
        
        # Window constraints
        opt.add(Implies(meet[i], T[i] >= window_start[i]))
        opt.add(Implies(meet[i], T[i] + min_duration[i] <= window_end[i]))
        opt.add(Implies(meet[i], T[i] >= 0))
    
    # Objective: maximize number of friends met
    obj = Sum([If(meet_i, 1, 0) for meet_i in meet])
    opt.maximize(obj)
    
    # Solve
    if opt.check() == sat:
        m = opt.model()
        total_met = sum(1 for i in range(5) if is_true(m[meet[i]]))
        print(f"Maximum number of friends met: {total_met}")
        for i in range(5):
            if is_true(m[meet[i]]):
                t_val = m[T[i]]
                if isinstance(t_val, IntNumRef):
                    minutes = t_val.as_long()
                elif isinstance(t_val, RatNumRef):
                    minutes = float(t_val.as_fraction())
                else:
                    minutes = 0
                hours = int(minutes) // 60
                mins = int(minutes) % 60
                arrival_time = f"{9 + hours}:{mins:02d}"
                print(f"Meet friend {i} at {arrival_time} (duration: {min_duration[i]} minutes)")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()