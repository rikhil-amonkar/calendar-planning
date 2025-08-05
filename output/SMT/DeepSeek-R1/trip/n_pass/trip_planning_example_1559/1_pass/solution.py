from z3 import *
import json

def main():
    cities = ['Lisbon', 'Paris', 'Lyon', 'Nice', 'Tallinn', 'Oslo', 'Prague', 'Valencia', 'Seville', 'Mykonos']
    idx = {city: i for i, city in enumerate(cities)}
    
    required_days = {
        'Lisbon': 2,
        'Paris': 4,
        'Lyon': 4,
        'Nice': 4,
        'Tallinn': 2,
        'Oslo': 3,
        'Prague': 3,
        'Valencia': 2,
        'Seville': 5,
        'Mykonos': 5
    }
    
    edges = [
        ('Lisbon', 'Paris'),
        ('Lyon', 'Nice'),
        ('Tallinn', 'Oslo'),
        ('Prague', 'Lyon'),
        ('Paris', 'Oslo'),
        ('Lisbon', 'Seville'),
        ('Prague', 'Lisbon'),
        ('Oslo', 'Nice'),
        ('Valencia', 'Paris'),
        ('Valencia', 'Lisbon'),
        ('Paris', 'Nice'),
        ('Nice', 'Mykonos'),
        ('Paris', 'Lyon'),
        ('Valencia', 'Lyon'),
        ('Prague', 'Oslo'),
        ('Prague', 'Paris'),
        ('Seville', 'Paris'),
        ('Oslo', 'Lyon'),
        ('Prague', 'Valencia'),
        ('Lisbon', 'Nice'),
        ('Lisbon', 'Oslo'),
        ('Valencia', 'Seville'),
        ('Lisbon', 'Lyon'),
        ('Paris', 'Tallinn'),
        ('Prague', 'Tallinn')
    ]
    
    adj = [[False] * 10 for _ in range(10)]
    for u, v in edges:
        i = idx[u]
        j = idx[v]
        adj[i][j] = True
        adj[j][i] = True
    
    allowed_pairs = []
    for i in range(10):
        for j in range(10):
            if adj[i][j]:
                allowed_pairs.append((i, j))
    
    s = Solver()
    
    order = [Int(f'order_{i}') for i in range(10)]
    for i in range(10):
        s.add(order[i] >= 0, order[i] < 10)
    s.add(Distinct(order))
    
    start = {city: Int(f'start_{city}') for city in cities}
    end = {city: Int(f'end_{city}') for city in cities}
    
    start_list = [Int(f'start_list_{i}') for i in range(10)]
    end_list = [Int(f'end_list_{i}') for i in range(10)]
    
    for city in cities:
        s.add(start[city] >= 1)
        s.add(start[city] <= 25)
        s.add(end[city] >= 1)
        s.add(end[city] <= 25)
        if city != 'Seville':
            s.add(end[city] == start[city] + (required_days[city] - 1))
    
    s.add(start['Seville'] == 5)
    s.add(end['Seville'] == 9)
    
    s.add(start['Valencia'] >= 2, start['Valencia'] <= 4)
    s.add(start['Oslo'] >= 11, start['Oslo'] <= 15)
    s.add(start['Mykonos'] >= 17, start['Mykonos'] <= 21)
    
    for i in range(10):
        for city in cities:
            c_index = idx[city]
            s.add(Implies(order[i] == c_index, start_list[i] == start[city]))
            s.add(Implies(order[i] == c_index, end_list[i] == end[city]))
    
    s.add(start_list[0] == 1)
    s.add(end_list[9] == 25)
    for i in range(9):
        s.add(end_list[i] == start_list[i+1])
    
    for i in range(9):
        or_conditions = []
        for a, b in allowed_pairs:
            or_conditions.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(or_conditions))
    
    if s.check() == sat:
        m = s.model()
        order_vals = [m[order[i]].as_long() for i in range(10)]
        city_sequence = [cities[idx] for idx in order_vals]
        
        start_vals = {}
        end_vals = {}
        for city in cities:
            start_vals[city] = m[start[city]].as_long()
            end_vals[city] = m[end[city]].as_long()
        
        itinerary = []
        for day in range(1, 26):
            for idx_val in order_vals:
                city = cities[idx_val]
                s_val = start_vals[city]
                e_val = end_vals[city]
                if s_val <= day <= e_val:
                    itinerary.append({"day": day, "city": city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()