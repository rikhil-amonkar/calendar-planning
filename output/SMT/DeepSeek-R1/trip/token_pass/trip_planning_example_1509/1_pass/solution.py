import json
from z3 import *

def main():
    # City names and their indices
    cities = ["Paris", "Warsaw", "Krakow", "Tallinn", "Riga", "Copenhagen", "Helsinki", "Oslo", "Santorini", "Lyon"]
    n = len(cities)
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Durations for each city (index order)
    d = [5, 2, 2, 2, 2, 5, 5, 5, 2, 4]
    
    # Flight connections (as city indices)
    flight_pairs = [
        ("Warsaw", "Riga"), ("Warsaw", "Tallinn"), ("Copenhagen", "Helsinki"),
        ("Lyon", "Paris"), ("Copenhagen", "Warsaw"), ("Lyon", "Oslo"),
        ("Paris", "Oslo"), ("Paris", "Riga"), ("Krakow", "Helsinki"),
        ("Paris", "Tallinn"), ("Oslo", "Riga"), ("Krakow", "Warsaw"),
        ("Paris", "Helsinki"), ("Copenhagen", "Santorini"), ("Helsinki", "Warsaw"),
        ("Helsinki", "Riga"), ("Copenhagen", "Krakow"), ("Copenhagen", "Riga"),
        ("Paris", "Krakow"), ("Copenhagen", "Oslo"), ("Oslo", "Tallinn"),
        ("Oslo", "Helsinki"), ("Copenhagen", "Tallinn"), ("Oslo", "Krakow"),
        ("Riga", "Tallinn"), ("Helsinki", "Tallinn"), ("Paris", "Copenhagen"),
        ("Paris", "Warsaw"), ("Santorini", "Oslo"), ("Oslo", "Warsaw")
    ]
    
    flight_set = set()
    for city1, city2 in flight_pairs:
        idx1 = city_index[city1]
        idx2 = city_index[city2]
        flight_set.add((min(idx1, idx2), max(idx1, idx2)))
    
    # Initialize Z3 solver
    solver = Solver()
    
    # Order of cities (10 integers representing city indices)
    order = [Int(f"order_{i}") for i in range(n)]
    for i in range(n):
        solver.add(order[i] >= 0, order[i] < n)
    solver.add(Distinct(order))
    
    # Start days for each city
    s = [Int(f"s_{i}") for i in range(n)]
    for i in range(n):
        solver.add(s[i] >= 1)
    
    # Constraints for start days based on order
    solver.add(s[order[0]] == 1)
    for i in range(1, n):
        solver.add(s[order[i]] == s[order[i-1]] + d[order[i-1]] - 1)
    solver.add(s[order[n-1]] + d[order[n-1]] - 1 == 25)
    
    # Event constraints
    # Paris (index0) must start by day 8
    solver.add(s[0] <= 8)
    # Krakow (index2) must start on day 17
    solver.add(s[2] == 17)
    # Riga (index4) must start on day 23
    solver.add(s[4] == 23)
    # Helsinki (index6) must start between day 14 and 22 (inclusive)
    solver.add(s[6] >= 14, s[6] <= 22)
    # Santorini (index8) must start on day 12
    solver.add(s[8] == 12)
    
    # Flight connectivity constraints
    for i in range(n-1):
        x = order[i]
        y = order[i+1]
        cond = False
        for (a, b) in flight_set:
            cond = Or(cond, And(x == a, y == b), And(x == b, y == a))
        solver.add(cond)
    
    # Check feasibility and get model
    if solver.check() == sat:
        model = solver.model()
        # Extract the order of cities
        visit_order = []
        for i in range(n):
            city_idx = model.evaluate(order[i]).as_long()
            visit_order.append(city_idx)
        
        # Extract start days for each city
        start_days = [0] * n
        for i in range(n):
            start_days[i] = model.evaluate(s[i]).as_long()
        
        # Build itinerary in the order of visitation
        itinerary = []
        for city_idx in visit_order:
            start = start_days[city_idx]
            end = start + d[city_idx] - 1
            day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": cities[city_idx]})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()