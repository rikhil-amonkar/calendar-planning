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
    
    # Trip sequence constraints using element-wise constraints
    # First city in order must have arrival day 1
    solver.add(And([If(order[0] == i, arr[i] == 1, True) for i in range(7)]))
    # Last city in order must have departure day 17
    solver.add(And([If(order[6] == i, dep[i] == 17, True) for i in range(7)]))
    
    # Consecutive cities must have matching departure and arrival
    for seg in range(6):
        current_city = order[seg]
        next_city = order[seg+1]
        solver.add(And([If(And(current_city == i, next_city == j), dep[i] == arr[j], True) 
                        for i in range(7) for j in range(7)]))
    
    # Flight constraints between consecutive cities
    for seg in range(6):
        city_i = order[seg]
        city_j = order[seg+1]
        # Create condition for flight existence
        flight_conditions = []
        for i in range(7):
            for j in range(7):
                if flights[i][j]:
                    flight_conditions.append(And(city_i == i, city_j == j))
        solver.add(Or(flight_conditions))
    
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