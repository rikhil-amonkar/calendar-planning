from z3 import *
import json

def main():
    # City indices
    cities = ['Brussels', 'Helsinki', 'Split', 'Dubrovnik', 'Istanbul', 'Milan', 'Vilnius', 'Frankfurt']
    req_days = [3, 3, 4, 2, 5, 4, 5, 3]
    
    # Build directed flight graph
    flights = []
    symmetric_flights = [
        "Milan and Frankfurt", "Split and Frankfurt", "Milan and Split",
        "Brussels and Vilnius", "Brussels and Helsinki", "Istanbul and Brussels",
        "Milan and Vilnius", "Brussels and Milan", "Istanbul and Helsinki",
        "Helsinki and Vilnius", "Helsinki and Dubrovnik", "Split and Vilnius",
        "Istanbul and Milan", "Helsinki and Frankfurt", "Istanbul and Vilnius",
        "Split and Helsinki", "Milan and Helsinki", "Istanbul and Frankfurt",
        "Dubrovnik and Frankfurt", "Frankfurt and Vilnius"
    ]
    
    for s in symmetric_flights:
        parts = s.split(' and ')
        c1 = cities.index(parts[0])
        c2 = cities.index(parts[1])
        flights.append((c1, c2))
        flights.append((c2, c1))
    
    asymmetric_flights = [
        "from Dubrovnik to Istanbul",
        "from Brussels to Frankfurt"
    ]
    
    for s in asymmetric_flights:
        parts = s.split()
        c1 = cities.index(parts[1])
        c2 = cities.index(parts[3])
        flights.append((c1, c2))
    
    # Z3 variables
    order = [Int('order_%d' % i) for i in range(8)]
    start = [Int('start_%d' % i) for i in range(8)]
    end = [Int('end_%d' % i) for i in range(8)]
    
    solver = Solver()
    
    # Order constraints
    solver.add([And(0 <= order[i], order[i] <= 7) for i in range(8)])
    solver.add(Distinct(order))
    
    # City constraints
    for i in range(8):
        solver.add(start[i] >= 1)
        solver.add(start[i] <= 22)
        solver.add(end[i] >= 1)
        solver.add(end[i] <= 22)
        solver.add(end[i] >= start[i])
        solver.add(end[i] - start[i] + 1 >= req_days[i])
    
    # Trip constraints
    solver.add(start[order[0]] == 1)
    solver.add(end[order[7]] == 22)
    for i in range(7):
        solver.add(end[order[i]] == start[order[i+1]])
    
    # Flight constraints
    for i in range(7):
        solver.add(Or([And(order[i] == f[0], order[i+1] == f[1]) for f in flights]))
    
    # Fixed events
    istanbul_idx = cities.index('Istanbul')
    vilnius_idx = cities.index('Vilnius')
    frankfurt_idx = cities.index('Frankfurt')
    
    solver.add(start[istanbul_idx] <= 1)
    solver.add(end[istanbul_idx] >= 5)
    solver.add(start[vilnius_idx] <= 18)
    solver.add(end[vilnius_idx] >= 22)
    solver.add(start[frankfurt_idx] <= 16)
    solver.add(end[frankfurt_idx] >= 18)
    
    # Total days constraint
    total_days = Sum([end[i] - start[i] + 1 for i in range(8)])
    solver.add(total_days == 29)
    
    if solver.check() == sat:
        model = solver.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(8)]
        start_val = [model.evaluate(start[i]).as_long() for i in range(8)]
        end_val = [model.evaluate(end[i]).as_long() for i in range(8)]
        
        itinerary = []
        for i in range(8):
            city_idx = order_val[i]
            s = start_val[city_idx]
            e = end_val[city_idx]
            if s == e:
                day_range = f"Day {s}"
            else:
                day_range = f"Day {s}-{e}"
            itinerary.append({"day_range": day_range, "place": cities[city_idx]})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()