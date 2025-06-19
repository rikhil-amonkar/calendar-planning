import z3
import json

def main():
    # City names and their indices
    city_names = ['Brussels', 'Bucharest', 'Stuttgart', 'Mykonos', 'Madrid', 'Helsinki', 'Split', 'London']
    name_to_index = {name: idx for idx, name in enumerate(city_names)}
    
    # Required days for each city
    required_days = [4, 3, 4, 2, 2, 5, 3, 5]  # Index order: 0 to 7
    
    # Direct flights (edges)
    edges_list = [
        ('Helsinki', 'London'),
        ('Split', 'Madrid'),
        ('Helsinki', 'Madrid'),
        ('London', 'Madrid'),
        ('Brussels', 'London'),
        ('Bucharest', 'London'),
        ('Brussels', 'Bucharest'),
        ('Bucharest', 'Madrid'),
        ('Split', 'Helsinki'),
        ('Mykonos', 'Madrid'),
        ('Stuttgart', 'London'),
        ('Helsinki', 'Brussels'),
        ('Brussels', 'Madrid'),
        ('Split', 'London'),
        ('Stuttgart', 'Split'),
        ('London', 'Mykonos')
    ]
    
    # Build the graph (adjacency matrix)
    graph = [[False] * 8 for _ in range(8)]
    for a, b in edges_list:
        i = name_to_index[a]
        j = name_to_index[b]
        graph[i][j] = True
        graph[j][i] = True
    
    # Z3 solver setup
    solver = z3.Solver()
    
    # Permutation variables: P[0] to P[7]
    P = [z3.Int(f'P_{i}') for i in range(8)]
    # Cumulative days variables
    Cum = [z3.Int(f'Cum_{i}') for i in range(8)]
    
    # Constraints
    # Each P[i] is between 0 and 7
    for i in range(8):
        solver.add(P[i] >= 0, P[i] < 8)
    
    # All cities are distinct
    solver.add(z3.Distinct(P))
    
    # Madrid is the last city (index 4 at position 7)
    solver.add(P[7] == 4)
    
    # Cumulative days constraints
    solver.add(Cum[0] == required_days[P[0]])
    for i in range(1, 8):
        solver.add(Cum[i] == Cum[i-1] + required_days[P[i]])
    
    # Flight constraints: consecutive cities must have a direct flight
    for i in range(7):
        # Create a condition for each allowed edge
        conditions = []
        for a in range(8):
            for b in range(8):
                if graph[a][b]:
                    conditions.append(z3.And(P[i] == a, P[i+1] == b))
        solver.add(z3.Or(conditions))
    
    # Stuttgart constraint (Stuttgart index is 2)
    for i in range(1, 8):  # positions 1 to 7
        stuttgart_here = (P[i] == 2)
        # s_i = Cum[i-1] - (i-1) <= 4
        constraint = (Cum[i-1] - (i - 1) <= 4)
        solver.add(z3.If(stuttgart_here, constraint, True))
    
    # Solve the problem
    if solver.check() == z3.sat:
        model = solver.model()
        # Extract the permutation
        p_val = [model.evaluate(P[i]).as_long() for i in range(8)]
        # Compute cumulative days from the permutation
        cum_val = [0] * 8
        cum_val[0] = required_days[p_val[0]]
        for i in range(1, 8):
            cum_val[i] = cum_val[i-1] + required_days[p_val[i]]
        
        # Compute start and end days for each stay
        starts = []
        ends = []
        for i in range(8):
            if i == 0:
                s_i = 1
            else:
                s_i = cum_val[i-1] - (i - 1)
            e_i = cum_val[i] - i
            starts.append(s_i)
            ends.append(e_i)
        
        # Build itinerary
        itinerary = []
        for i in range(8):
            city = city_names[p_val[i]]
            # Contiguous stay
            itinerary.append({"day_range": f"Day {starts[i]}-{ends[i]}", "place": city})
            if i < 7:
                # Flight day: departure from current city and arrival at next city
                d = ends[i]
                itinerary.append({"day_range": f"Day {d}", "place": city})
                itinerary.append({"day_range": f"Day {d}", "place": city_names[p_val[i+1]]})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()