import z3
import json

def main():
    cities = ['Rome', 'Mykonos', 'Lisbon', 'Frankfurt', 'Nice', 'Stuttgart', 'Venice', 'Dublin', 'Bucharest', 'Seville']
    days_required = [3, 2, 2, 5, 3, 4, 4, 2, 2, 5]
    
    # Flight connection graph (adjacency matrix)
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
    
    # Build flight connection graph
    city_index = {city: idx for idx, city in enumerate(cities)}
    for pair in flight_pairs:
        city1, city2 = pair.split(" and ")
        idx1 = city_index[city1]
        idx2 = city_index[city2]
        graph[idx1][idx2] = 1
        graph[idx2][idx1] = 1
    
    # Indices for specific cities
    frankfurt_idx = city_index['Frankfurt']
    seville_idx = city_index['Seville']
    mykonos_idx = city_index['Mykonos']
    
    # Initialize Z3 solver and variables
    s = z3.Solver()
    
    # Sequence of cities (order of visit)
    seq = [z3.Int(f'seq_{i}') for i in range(10)]
    # Start and end days for each city
    starts = [z3.Int(f'start_{i}') for i in range(10)]
    ends = [z3.Int(f'end_{i}') for i in range(10)]
    
    # Sequence must be a permutation of cities
    for i in range(10):
        s.add(seq[i] >= 0, seq[i] < 10)
    s.add(z3.Distinct(seq))
    s.add(seq[0] == frankfurt_idx)  # Frankfurt is first city
    
    # Frankfurt covers days 1-5
    s.add(starts[frankfurt_idx] == 1)
    s.add(ends[frankfurt_idx] == 5)
    
    # Seville covers days 13-17
    s.add(starts[seville_idx] == 13)
    s.add(ends[seville_idx] == 17)
    
    # Mykonos must include at least one day between 10-11
    s.add(z3.Or(
        z3.And(starts[mykonos_idx] <= 10, ends[mykonos_idx] >= 10),
        z3.And(starts[mykonos_idx] <= 11, ends[mykonos_idx] >= 11)
    ))
    
    # Duration constraints
    for i in range(10):
        s.add(ends[i] - starts[i] + 1 == days_required[i])
        s.add(starts[i] >= 1, ends[i] <= 23)  # Trip within 23 days
    
    # Last city ends on day 23
    s.add(ends[seq[9]] == 23)
    
    # Consecutive cities must have overlapping flight days
    for i in range(9):
        current_city = seq[i]
        next_city = seq[i+1]
        s.add(ends[current_city] == starts[next_city])
    
    # Flight connections between consecutive cities
    for i in range(9):
        current_city = seq[i]
        next_city = seq[i+1]
        s.add(graph[current_city][next_city] == 1)
    
    # Solve and output itinerary
    if s.check() == z3.sat:
        m = s.model()
        seq_val = [m.evaluate(seq[i]).as_long() for i in range(10)]
        start_val = [m.evaluate(starts[i]).as_long() for i in range(10)]
        end_val = [m.evaluate(ends[i]).as_long() for i in range(10)]
        
        itinerary = []
        for i in range(10):
            city_idx = seq_val[i]
            itinerary.append({
                'day_range': f'Day {start_val[city_idx]}-{end_val[city_idx]}',
                'place': cities[city_idx]
            })
        
        print(json.dumps({'itinerary': itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()