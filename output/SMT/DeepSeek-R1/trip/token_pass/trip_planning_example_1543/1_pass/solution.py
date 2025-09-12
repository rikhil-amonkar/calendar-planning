import json
from z3 import *

def main():
    cities = ["Prague", "Warsaw", "Dublin", "Athens", "Vilnius", "Porto", "London", "Seville", "Lisbon", "Dubrovnik"]
    required_days = [3, 4, 3, 3, 4, 5, 3, 2, 5, 3]
    direct_flights = [
        ("Warsaw", "Vilnius"), ("Prague", "Athens"), ("London", "Lisbon"), ("Lisbon", "Porto"),
        ("Prague", "Lisbon"), ("London", "Dublin"), ("Athens", "Vilnius"), ("Athens", "Dublin"),
        ("Prague", "London"), ("London", "Warsaw"), ("Dublin", "Seville"), ("Seville", "Porto"),
        ("Lisbon", "Athens"), ("Dublin", "Porto"), ("Athens", "Warsaw"), ("Lisbon", "Warsaw"),
        ("Porto", "Warsaw"), ("Prague", "Warsaw"), ("Prague", "Dublin"), ("Athens", "Dubrovnik"),
        ("Lisbon", "Dublin"), ("Dubrovnik", "Dublin"), ("Lisbon", "Seville"), ("London", "Athens")
    ]
    
    direct_flights_set = set()
    for a, b in direct_flights:
        i = cities.index(a)
        j = cities.index(b)
        direct_flights_set.add((i, j))
        direct_flights_set.add((j, i))
    
    solver = Solver()
    
    base_city = [Int(f'base_city_{d}') for d in range(1, 27)]
    for bc in base_city:
        solver.add(bc >= 0, bc < 10)
    
    in_city = [[Bool(f'in_city_{c}_{d}') for d in range(1, 27)] for c in range(10)]
    
    for d in range(26):
        day_index = d
        for c in range(10):
            solver.add(Implies(base_city[d] == c, in_city[c][d]))
        if d < 25:
            for c in range(10):
                solver.add(Implies(
                    And(base_city[d] != base_city[d+1], base_city[d+1] == c),
                    in_city[c][d]
                ))
    
    fixed_constraints = [
        (0, [1, 2, 3]),
        (1, [20, 21, 22, 23]),
        (5, [16, 17, 18, 19, 20]),
        (6, [3, 4, 5]),
        (8, [5, 6, 7, 8, 9])
    ]
    
    for city_index, days in fixed_constraints:
        for d in days:
            solver.add(in_city[city_index][d-1])
    
    for c in range(10):
        total = 0
        for d in range(26):
            total += If(in_city[c][d], 1, 0)
        solver.add(total == required_days[c])
    
    for d in range(25):
        cond = (base_city[d] != base_city[d+1])
        allowed_pairs = []
        for (i, j) in direct_flights_set:
            allowed_pairs.append(And(base_city[d] == i, base_city[d+1] == j))
        solver.add(Implies(cond, Or(allowed_pairs)))
    
    if solver.check() == sat:
        model = solver.model()
        base_city_values = []
        for d in range(26):
            val = model.evaluate(base_city[d])
            base_city_values.append(val.as_long())
        
        itinerary = []
        current_city_index = base_city_values[0]
        start_day = 1
        for day in range(1, 26):
            if base_city_values[day] != current_city_index:
                end_day = day
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}",
                    "place": cities[current_city_index]
                })
                current_city_index = base_city_values[day]
                start_day = day + 1
        itinerary.append({
            "day_range": f"Day {start_day}-26",
            "place": cities[current_city_index]
        })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()