from z3 import *
import json

def main():
    # Cities and their indices
    cities = ['Rome', 'Santorini', 'Seville', 'Istanbul', 'Naples']
    n_cities = len(cities)
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Required days per city
    req_days = [0] * n_cities
    req_days[city_index['Istanbul']] = 2
    req_days[city_index['Rome']] = 3
    req_days[city_index['Seville']] = 4
    req_days[city_index['Naples']] = 7
    req_days[city_index['Santorini']] = 4
    
    # Direct flights as tuples of indices
    direct_flights = [
        ('Rome', 'Santorini'),
        ('Seville', 'Rome'),
        ('Istanbul', 'Naples'),
        ('Naples', 'Santorini'),
        ('Rome', 'Naples'),
        ('Rome', 'Istanbul')
    ]
    direct_flights_set = set()
    for a, b in direct_flights:
        idx_a = city_index[a]
        idx_b = city_index[b]
        if idx_a < idx_b:
            direct_flights_set.add((idx_a, idx_b))
        else:
            direct_flights_set.add((idx_b, idx_a))
    
    # Initialize solver
    s = Solver()
    
    # city_end[0] to city_end[16] variables
    city_end = [Int('city_end_%d' % i) for i in range(17)]
    
    # Each variable must be between 0 and 4
    for i in range(17):
        s.add(city_end[i] >= 0, city_end[i] < n_cities)
    
    # Flight constraints between consecutive days
    for i in range(1, 17):
        prev = city_end[i-1]
        curr = city_end[i]
        s.add(If(prev != curr, 
                 Or([And(prev == a, curr == b) for (a, b) in direct_flights_set] + 
                    [And(prev == b, curr == a) for (a, b) in direct_flights_set]),
                 True))
    
    # Total days per city constraint
    for c in range(n_cities):
        total = 0
        for i in range(1, 17):
            total += If(Or(city_end[i-1] == c, city_end[i] == c), 1, 0)
        s.add(total == req_days[c])
    
    # Specific day constraints
    istanbul_idx = city_index['Istanbul']
    santorini_idx = city_index['Santorini']
    
    # Istanbul on days 6 and 7
    s.add(Or(city_end[5] == istanbul_idx, city_end[6] == istanbul_idx))
    s.add(Or(city_end[6] == istanbul_idx, city_end[7] == istanbul_idx))
    
    # Santorini on days 13 to 16
    s.add(Or(city_end[12] == santorini_idx, city_end[13] == santorini_idx))
    s.add(Or(city_end[13] == santorini_idx, city_end[14] == santorini_idx))
    s.add(Or(city_end[14] == santorini_idx, city_end[15] == santorini_idx))
    s.add(Or(city_end[15] == santorini_idx, city_end[16] == santorini_idx))
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        city_end_values = [m.evaluate(city_end[i]).as_long() for i in range(17)]
        
        itinerary = []
        start = 1
        current_city_idx = city_end_values[1]
        for day in range(2, 17):
            if city_end_values[day] != current_city_idx:
                end_day = day
                itinerary.append({
                    "day_range": f"Day {start}-{end_day}",
                    "place": cities[current_city_idx]
                })
                start = day + 1
                current_city_idx = city_end_values[day]
        itinerary.append({
            "day_range": f"Day {start}-16",
            "place": cities[current_city_idx]
        })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()