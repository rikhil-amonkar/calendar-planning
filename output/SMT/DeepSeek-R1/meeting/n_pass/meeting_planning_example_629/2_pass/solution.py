from z3 import *

def main():
    # Meetings by node: {node: (name, min_duration, available_start (minutes from 9:00), available_end)}
    meetings_by_node = {
        1: ("Matthew", 90, 120, 720),     # Presidio, 11:00-21:00
        2: ("Margaret", 90, 15, 585),      # Chinatown, 9:15-18:45
        3: ("Nancy", 15, 315, 480),        # Pacific Heights, 14:15-17:00
        4: ("Helen", 60, 645, 780),        # Richmond District, 19:45-22:00
        5: ("Rebecca", 60, 735, 795),      # Fisherman's Wharf, 21:15-22:15
        6: ("Kimberly", 120, 240, 450),    # Golden Gate Park, 13:00-16:30
        7: ("Kenneth", 60, 330, 540)       # Bayview, 14:30-18:00
    }
    
    # Travel times: 8x8 matrix, indexed [start_node][end_node]
    travel_matrix = [
        [0, 14, 9, 7, 14, 7, 21, 23],    # 0: Russian Hill
        [14, 0, 21, 11, 7, 19, 12, 31],  # 1: Presidio
        [7, 19, 0, 10, 20, 8, 23, 22],    # 2: Chinatown
        [7, 11, 11, 0, 12, 13, 15, 22],   # 3: Pacific Heights
        [13, 7, 20, 10, 0, 18, 9, 26],    # 4: Richmond District
        [7, 17, 12, 12, 18, 0, 25, 26],   # 5: Fisherman's Wharf
        [19, 11, 23, 16, 7, 24, 0, 23],   # 6: Golden Gate Park
        [23, 31, 18, 23, 25, 25, 22, 0]   # 7: Bayview
    ]
    
    nodes = [1, 2, 3, 4, 5, 6, 7]
    
    # Create the solver
    opt = Optimize()
    
    # Variables: visit[j] for j in nodes, s[j] for start time of node j
    visit = { j: Bool(f'visit_{j}') for j in nodes }
    s = { j: Real(f's_{j}') for j in nodes }
    
    # x[(i, j)] for i in [0,7] and j in nodes, i != j
    x = {}
    for i in range(0, 8):
        for j in nodes:
            if i != j:
                x[(i, j)] = Bool(f'x_{i}_{j}')
    
    # Constraint 1: Start node (0) has at most one outgoing
    opt.add(Sum([x[(0, j)] for j in nodes]) <= 1)
    
    # Constraint 2: For each node j in nodes
    for j in nodes:
        # Incoming arcs: from any i (0-7, i != j)
        incoming = Sum([x[(i, j)] for i in range(0, 8) if i != j])
        opt.add(incoming == visit[j])
        
        # Outgoing arcs: to any k in nodes (k != j)
        outgoing = Sum([x[(j, k)] for k in nodes if k != j])
        opt.add(outgoing <= visit[j])
        
        # Time window constraints
        name, dur, start_avail, end_avail = meetings_by_node[j]
        opt.add(If(visit[j],
                   And(s[j] >= start_avail, s[j] + dur <= end_avail),
                   True))
    
    # Constraint 3: Travel constraints
    for i in range(0, 8):
        for j in nodes:
            if i == j:
                continue
            if i == 0:
                # From start node (0) to node j
                opt.add(Implies(x[(i, j)], s[j] >= travel_matrix[i][j]))
            else:
                # From node i to node j (i in [1,7])
                dur_i = meetings_by_node[i][1]
                opt.add(Implies(x[(i, j)], s[j] >= s[i] + dur_i + travel_matrix[i][j]))
    
    # Non-negative start times
    for j in nodes:
        opt.add(s[j] >= 0)
    
    # Objective: maximize number of visited meetings
    total_meetings = Sum([If(visit[j], 1, 0) for j in nodes])
    opt.maximize(total_meetings)
    
    # Solve
    if opt.check() == sat:
        model = opt.model()
        # Build the itinerary by following the chain
        current = 0
        chain = []
        # Find the first meeting
        for j in nodes:
            if is_true(model[x[(0, j)]]):
                chain.append(j)
                current = j
                break
        # Traverse the chain
        while True:
            next_node = None
            for k in nodes:
                if k == current:
                    continue
                if is_true(model[x[(current, k)]]):
                    next_node = k
                    break
            if next_node is None:
                break
            chain.append(next_node)
            current = next_node
        
        itinerary = []
        for j in chain:
            name, dur, _, _ = meetings_by_node[j]
            start_val = model[s[j]]
            # Convert Z3 Real to integer
            if is_int_value(start_val):
                start_minutes = start_val.as_long()
            elif is_rational_value(start_val):
                start_minutes = start_val.numerator_as_long() // start_val.denominator_as_long()
            else:
                # Fallback: try to convert from string
                start_minutes = int(str(model[s[j]]).split('/')[0])
            end_minutes = start_minutes + dur
            # Convert minutes to time string
            start_hour = 9 + start_minutes // 60
            start_minute = start_minutes % 60
            end_hour = 9 + end_minutes // 60
            end_minute = end_minutes % 60
            start_str = f"{start_hour:02d}:{start_minute:02d}"
            end_str = f"{end_hour:02d}:{end_minute:02d}"
            itinerary.append({
                "action": "meet",
                "person": name,
                "start_time": start_str,
                "end_time": end_str
            })
        
        # Output the itinerary in JSON format
        print('SOLUTION:')
        print(f'{{"itinerary": {itinerary}}}')
    else:
        print("No solution found")

if __name__ == "__main__":
    main()