from z3 import *
import json

def main():
    # City mapping
    cities = ['Dubrovnik', 'Warsaw', 'Stuttgart', 'Bucharest', 'Copenhagen']
    city_map = {c: i for i, c in enumerate(cities)}
    
    # Requirements
    req_days = [5, 2, 7, 6, 3]  # Corresponding to cities order
    
    # Direct flights (as city indices)
    flights = [
        (city_map['Warsaw'], city_map['Copenhagen']),
        (city_map['Stuttgart'], city_map['Copenhagen']),
        (city_map['Warsaw'], city_map['Stuttgart']),
        (city_map['Bucharest'], city_map['Copenhagen']),
        (city_map['Bucharest'], city_map['Warsaw']),
        (city_map['Copenhagen'], city_map['Dubrovnik'])
    ]
    
    # Create allowed pairs (symmetric)
    allowed_pairs = set()
    for a, b in flights:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    
    # Initialize solver
    s = Solver()
    
    # Variables: x1 to x20 (0-indexed list for x1 to x20)
    x = [Int(f'x_{i}') for i in range(1, 21)]
    for i in range(20):
        s.add(x[i] >= 0, x[i] < 5)
    
    # Flight constraints
    for i in range(19):
        a = x[i]
        b = x[i+1]
        # If changing cities, ensure direct flight exists
        constraint = Or([And(a == pair[0], b == pair[1]) for pair in allowed_pairs])
        s.add(If(a != b, constraint, True))
    
    # Total days per city
    for c_idx, required in enumerate(req_days):
        total = 0
        for i in range(19):
            # Count morning city
            total += If(x[i] == c_idx, 1, 0)
            # Count arrival city if flight day
            total += If(And(x[i] != x[i+1], x[i+1] == c_idx), 1, 0)
        s.add(total == required)
    
    # Conference constraints
    stuttgart_idx = city_map['Stuttgart']
    # Day 7: x6 (morning) and x7 (next morning)
    s.add(Or(x[6] == stuttgart_idx, And(x[6] != x[7], x[7] == stuttgart_idx)))
    # Day 13: x12 and x13
    s.add(Or(x[12] == stuttgart_idx, And(x[12] != x[13], x[13] == stuttgart_idx)))
    
    # Wedding constraint (at least one day in 1-6 in Bucharest)
    bucharest_idx = city_map['Bucharest']
    wedding_constraints = []
    for i in range(6):
        # Check if day i+1 is in Bucharest
        in_bucharest = Or(x[i] == bucharest_idx, And(x[i] != x[i+1], x[i+1] == bucharest_idx))
        wedding_constraints.append(in_bucharest)
    s.add(Or(wedding_constraints))
    
    # Check feasibility
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(19):
            day_num = i + 1
            city1_idx = m.evaluate(x[i]).as_long()
            city2_idx = m.evaluate(x[i+1]).as_long()
            city1 = cities[city1_idx]
            if city1_idx != city2_idx:
                city2 = cities[city2_idx]
                place = f"{city1} and {city2}"
            else:
                place = city1
            itinerary.append({"day_range": f"Day {day_num}", "place": place})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"error": "No valid itinerary found"}')

if __name__ == '__main__':
    main()