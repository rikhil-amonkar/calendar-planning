import z3
import json

def main():
    cities = ['Rome', 'Mykonos', 'Lisbon', 'Frankfurt', 'Nice', 'Stuttgart', 'Venice', 'Dublin', 'Bucharest', 'Seville']
    days_required = [3, 2, 2, 5, 3, 4, 4, 2, 2, 5]
    
    # Flight connection graph
    graph = [[0]*10 for _ in range(10)]
    flight_pairs = [
        "Rome and Stuttgart", "Venice and Rome", "Dublin and Bucharest", "Mykonos and Rome",
        "Seville and Lisbon", "Frankfurt and Venice", "Venice and Stuttgart", "Bucharest and Lisbon",
        "Nice and Mykonos", "Venice and Lisbon", "Dublin and Lisbon", "Venice and Nice",
        "Rome and Seville", "Frankfurt and Rome", "Nice and Dublin", "Rome and Bucharest",
        "Frankfurt and Dublin", "Rome and Dublin", "Venice and Dublin", "Rome and Lisbon",
        "Frankfurt and Lisbon", "Nice and Rome", "Frankfurt and Nice", "Frankfurt and Stuttgart",
        "Frankfurt and Bucharest", "Lisbon and Stuttgart", "Nice and Lisbon", "Seville and Dublin"
    ]
    
    # Build graph
    city_index = {city: idx for idx, city in enumerate(cities)}
    for pair in flight_pairs:
        city1, city2 = pair.split(" and ")
        idx1 = city_index[city1]
        idx2 = city_index[city2]
        graph[idx1][idx2] = 1
        graph[idx2][idx1] = 1
    
    # Precompute edge list
    edge_list = []
    for j in range(10):
        for k in range(10):
            if graph[j][k] == 1:
                edge_list.append((j, k))
    
    # City indices
    frankfurt_idx = city_index['Frankfurt']
    seville_idx = city_index['Seville']
    mykonos_idx = city_index['Mykonos']
    
    # Initialize solver
    s = z3.Solver()
    
    # Variables
    seq = [z3.Int(f'seq_{i}') for i in range(10)]
    starts = [z3.Int(f'start_{i}') for i in range(10)]
    ends = [z3.Int(f'end_{i}') for i in range(10)]
    seq_starts = [z3.Int(f'seq_start_{i}') for i in range(10)]
    seq_ends = [z3.Int(f'seq_end_{i}') for i in range(10)]
    
    # Sequence constraints
    for i in range(10):
        s.add(seq[i] >= 0, seq[i] < 10)
    s.add(z3.Distinct(seq))
    s.add(seq[0] == frankfurt_idx)  # Frankfurt first
    
    # Fixed stays
    s.add(starts[frankfurt_idx] == 1, ends[frankfurt_idx] == 5)  # Frankfurt
    s.add(starts[seville_idx] == 13, ends[seville_idx] == 17)    # Seville
    
    # Mykonos constraint
    s.add(z3.Or(
        z3.And(starts[mykonos_idx] <= 10, ends[mykonos_idx] >= 10),
        z3.And(starts[mykonos_idx] <= 11, ends[mykonos_idx] >= 11)
    ))
    
    # Duration constraints
    for i in range(10):
        s.add(ends[i] - starts[i] + 1 == days_required[i])
        s.add(starts[i] >= 1, ends[i] <= 23)
    
    # Link sequence positions to city days
    for i in range(10):
        for j in range(10):
            s.add(z3.Implies(seq[i] == j, seq_starts[i] == starts[j]))
            s.add(z3.Implies(seq[i] == j, seq_ends[i] == ends[j]))
    
    # Consecutive day constraints
    for i in range(9):
        s.add(seq_ends[i] == seq_starts[i+1])
    
    # Last city ends on day 23
    s.add(seq_ends[9] == 23)
    
    # Flight connections
    for i in range(9):
        cons = z3.Or([z3.And(seq[i] == j, seq[i+1] == k) for (j, k) in edge_list])
        s.add(cons)
    
    # Solve
    if s.check() == z3.sat:
        m = s.model()
        itinerary = []
        for i in range(10):
            city_idx = m.evaluate(seq[i]).as_long()
            start = m.evaluate(seq_starts[i]).as_long()
            end = m.evaluate(seq_ends[i]).as_long()
            itinerary.append({
                'day_range': f'Day {start}-{end}',
                'place': cities[city_idx]
            })
        print(json.dumps({'itinerary': itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()