from z3 import *
import json

def main():
    # City indices and stay durations
    cities = {
        'Riga': 0,
        'Manchester': 1,
        'Bucharest': 2,
        'Florence': 3,
        'Vienna': 4,
        'Istanbul': 5,
        'Reykjavik': 6,
        'Stuttgart': 7
    }
    days = [4, 5, 4, 4, 2, 2, 4, 5]  # in order of city indices
    city_names = ['Riga', 'Manchester', 'Bucharest', 'Florence', 'Vienna', 'Istanbul', 'Reykjavik', 'Stuttgart']
    
    # Define the edges (undirected) as a set of tuples (a, b) with a < b
    edges_set = set([
        (0, 1), (0, 2), (0, 4), (0, 5),
        (1, 2), (1, 4), (1, 5), (1, 7),
        (2, 4), (2, 5),
        (3, 4),
        (4, 5), (4, 6), (4, 7),
        (5, 7),
        (6, 7)
    ])
    directed_edges = []
    for (a, b) in edges_set:
        directed_edges.append((a, b))
        directed_edges.append((b, a))
    
    # Create Z3 variables for the sequence of cities (8 elements)
    seq = [Int(f'seq_{i}') for i in range(8)]
    # Constraints: each element in seq is between 0 and 7
    seq_constraints = [And(seq[i] >= 0, seq[i] <= 7) for i in range(8)]
    # Distinct constraint
    distinct_constraint = Distinct(seq)
    
    # Cumulative sums for start day calculations
    cumul = [Int(f'cumul_{i}') for i in range(9)]
    cumul_constraints = [cumul[0] == 0]
    for i in range(8):
        val = None
        for j in range(8):
            if val is None:
                val = If(seq[i] == j, days[j] - 1, 0)
            else:
                val = If(seq[i] == j, days[j] - 1, val)
        cumul_constraints.append(cumul[i+1] == cumul[i] + val)
    
    # Position of Istanbul (city index 5) in the sequence
    pos_istanbul = Int('pos_istanbul')
    istanbul_pos_expr = Sum([If(seq[i] == 5, i, 0) for i in range(8)])
    istanbul_constraint = (pos_istanbul == istanbul_pos_expr)
    # Start day of Istanbul: 1 + cumul[pos_istanbul]
    start_istanbul_expr = 1 + If(pos_istanbul == 0, cumul[0],
                         If(pos_istanbul == 1, cumul[1],
                         If(pos_istanbul == 2, cumul[2],
                         If(pos_istanbul == 3, cumul[3],
                         If(pos_istanbul == 4, cumul[4],
                         If(pos_istanbul == 5, cumul[5],
                         If(pos_istanbul == 6, cumul[6],
                         If(pos_istanbul == 7, cumul[7], -1000)))))))  # -1000 is a placeholder, should not happen
    istanbul_constraint2 = (start_istanbul_expr == 12)
    
    # Position of Bucharest (city index 2) in the sequence
    pos_bucharest = Int('pos_bucharest')
    bucharest_pos_expr = Sum([If(seq[i] == 2, i, 0) for i in range(8)])
    bucharest_constraint = (pos_bucharest == bucharest_pos_expr)
    # Start and end days for Bucharest
    start_bucharest_expr = 1 + If(pos_bucharest == 0, cumul[0],
                         If(pos_bucharest == 1, cumul[1],
                         If(pos_bucharest == 2, cumul[2],
                         If(pos_bucharest == 3, cumul[3],
                         If(pos_bucharest == 4, cumul[4],
                         If(pos_bucharest == 5, cumul[5],
                         If(pos_bucharest == 6, cumul[6],
                         If(pos_bucharest == 7, cumul[7], -1000)))))))
    end_bucharest_expr = start_bucharest_expr + 3  # because 4 days: end = start + 3
    bucharest_constraint2 = And(start_bucharest_expr <= 19, end_bucharest_expr >= 16)
    
    # Flight constraints between consecutive cities
    flight_constraints = []
    for i in range(7):
        options = []
        for (a, b) in directed_edges:
            options.append(And(seq[i] == a, seq[i+1] == b))
        flight_constraints.append(Or(options))
    
    # Combine all constraints
    s = Solver()
    s.add(seq_constraints)
    s.add(distinct_constraint)
    s.add(cumul_constraints)
    s.add(istanbul_constraint)
    s.add(istanbul_constraint2)
    s.add(bucharest_constraint)
    s.add(bucharest_constraint2)
    s.add(flight_constraints)
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        seq_val = [m.evaluate(seq[i]).as_long() for i in range(8)]
        
        # Compute cumulative days from the sequence
        cumul_computed = [0]
        for i in range(8):
            c_index = seq_val[i]
            add = days[c_index] - 1
            cumul_computed.append(cumul_computed[-1] + add)
        
        # Build itinerary
        itinerary = []
        for i in range(8):
            c_index = seq_val[i]
            city_name = city_names[c_index]
            start_day = 1 + cumul_computed[i]
            end_day = start_day + days[c_index] - 1
            itinerary.append({"city": city_name, "start": start_day, "end": end_day})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()