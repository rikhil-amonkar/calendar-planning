from z3 import *
import json

def main():
    # City indices
    cities = ['Seville', 'Vilnius', 'Santorini', 'London', 'Stuttgart', 'Dublin', 'Frankfurt']
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Required days per city
    req_days = [5, 3, 2, 2, 3, 3, 5]
    
    # Direct flights (bidirectional)
    flight_pairs = [
        ('Frankfurt', 'Dublin'),
        ('Frankfurt', 'London'),
        ('London', 'Dublin'),
        ('Vilnius', 'Frankfurt'),
        ('Frankfurt', 'Stuttgart'),
        ('Dublin', 'Seville'),
        ('London', 'Santorini'),
        ('Stuttgart', 'London'),
        ('Santorini', 'Dublin')
    ]
    
    # Create flight graph (undirected)
    flights = [[False] * 7 for _ in range(7)]
    for city1, city2 in flight_pairs:
        idx1 = city_index[city1]
        idx2 = city_index[city2]
        flights[idx1][idx2] = True
        flights[idx2][idx1] = True

    # Z3 solver
    solver = Solver()
    
    # Order of cities visited (7 segments)
    order = [Int(f'order_{i}') for i in range(7)]
    for o in order:
        solver.add(0 <= o, o < 7)
    solver.add(Distinct(order))
    
    # Arrival and departure days for each city
    arr = [Int(f'arr_{i}') for i in range(7)]
    dep = [Int(f'dep_{i}') for i in range(7)]
    for i in range(7):
        solver.add(arr[i] >= 1, arr[i] <= 17)
        solver.add(dep[i] >= 1, dep[i] <= 17)
        solver.add(dep[i] - arr[i] + 1 == req_days[i])
    
    # Trip sequence constraints
    solver.add(arr[order[0]] == 1)
    solver.add(dep[order[6]] == 17)
    for i in range(6):
        solver.add(dep[order[i]] == arr[order[i+1]])
    
    # Flight constraints between consecutive cities
    for i in range(6):
        city_i = order[i]
        city_j = order[i+1]
        # Ensure there's a flight between consecutive cities
        solver.add(Or([And(city_i == idx1, city_j == idx2) 
                      for idx1 in range(7) for idx2 in range(7) 
                      if flights[idx1][idx2]]))
    
    # Specific constraints
    london_idx = city_index['London']
    stuttgart_idx = city_index['Stuttgart']
    solver.add(arr[london_idx] <= 9, dep[london_idx] >= 10)
    solver.add(arr[stuttgart_idx] <= 7, dep[stuttgart_idx] >= 9)
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        
        # Get order from model
        visit_order = [model.evaluate(o).as_long() for o in order]
        
        # Get arrival and departure days
        arr_days = [model.evaluate(a).as_long() for a in arr]
        dep_days = [model.evaluate(d).as_long() for d in dep]
        
        # Build itinerary segments
        itinerary = []
        for i, city_idx in enumerate(visit_order):
            city_name = cities[city_idx]
            start_day = arr_days[city_idx]
            end_day = dep_days[city_idx]
            day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city_name})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No solution found')

if __name__ == '__main__':
    main()