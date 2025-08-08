from z3 import *
import json

def main():
    cities = ['Reykjavik', 'Stockholm', 'Porto', 'Nice', 'Venice', 'Vienna', 'Split', 'Copenhagen']
    name_to_index = {city: idx for idx, city in enumerate(cities)}
    days_req = [2, 2, 5, 3, 4, 3, 3, 2]
    
    flight_pairs = [
        ('Copenhagen', 'Vienna'),
        ('Nice', 'Stockholm'),
        ('Split', 'Copenhagen'),
        ('Nice', 'Reykjavik'),
        ('Nice', 'Porto'),
        ('Reykjavik', 'Vienna'),
        ('Stockholm', 'Copenhagen'),
        ('Nice', 'Venice'),
        ('Nice', 'Vienna'),
        ('Reykjavik', 'Copenhagen'),
        ('Nice', 'Copenhagen'),
        ('Stockholm', 'Vienna'),
        ('Venice', 'Vienna'),
        ('Copenhagen', 'Porto'),
        ('Reykjavik', 'Stockholm'),
        ('Stockholm', 'Split'),
        ('Split', 'Vienna'),
        ('Copenhagen', 'Venice'),
        ('Vienna', 'Porto')
    ]
    
    edges_set = set()
    for a, b in flight_pairs:
        i1 = name_to_index[a]
        i2 = name_to_index[b]
        edges_set.add((i1, i2))
        edges_set.add((i2, i1))
    
    s = Solver()
    
    position = [Int(f'pos_{i}') for i in range(8)]
    for p in position:
        s.add(p >= 0, p < 8)
    s.add(Distinct(position))
    
    city_pos = [Int(f'city_pos_{j}') for j in range(8)]
    for j in range(8):
        s.add(city_pos[j] >= 0, city_pos[j] < 8)
        or_terms = []
        for i in range(8):
            or_terms.append(And(city_pos[j] == i, position[i] == j))
        s.add(Or(or_terms))
    
    for i in range(7):
        u = position[i]
        v = position[i+1]
        s.add(Or([And(u == a, v == b) for (a, b) in edges_set]))
    
    cum = [Int(f'cum_{i}') for i in range(9)]
    s.add(cum[0] == 1)
    for k in range(8):
        d_k = Int(f'd_{k}')
        s.add(d_k == Sum([If(position[k] == j, days_req[j], 0) for j in range(8)]))
        s.add(cum[k+1] == cum[k] + d_k - 1)
        s.add(cum[k+1] > cum[k])
    s.add(cum[8] == 17)
    
    # Reykjavik (city0) must include day 3 or 4
    start0 = Int('start0')
    s.add(start0 == Sum([If(city_pos[0] == k, cum[k], 0) for k in range(8)]))
    s.add(start0 >= 2, start0 <= 4)
    
    # Vienna (city5) must include day 11, 12 or 13
    start5 = Int('start5')
    s.add(start5 == Sum([If(city_pos[5] == k, cum[k], 0) for k in range(8)]))
    s.add(start5 >= 9, start5 <= 13)
    
    # Porto (city2) must include at least one day from 13-17
    start2 = Int('start2')
    s.add(start2 == Sum([If(city_pos[2] == k, cum[k], 0) for k in range(8)]))
    s.add(start2 >= 9, start2 <= 13)
    
    if s.check() == sat:
        model = s.model()
        pos_val = [model.evaluate(position[i]).as_long() for i in range(8)]
        cum_val = [model.evaluate(cum[i]).as_long() for i in range(9)]
        city_pos_val = [model.evaluate(city_pos[j]).as_long() for j in range(8)]
        
        # Build day-by-day itinerary
        itinerary = []
        for day in range(1, 18):  # Days 1 to 17
            current_places = []
            for seq_idx in range(8):
                city_idx = pos_val[seq_idx]
                start = cum_val[seq_idx]
                end = start + days_req[city_idx] - 1
                if start <= day <= end:
                    current_places.append(cities[city_idx])
            itinerary.append({"day": day, "place": ", ".join(current_places)})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()