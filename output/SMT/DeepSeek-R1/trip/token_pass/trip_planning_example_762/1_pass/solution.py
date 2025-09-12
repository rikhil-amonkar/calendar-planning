import json
from z3 import *

def main():
    # Cities and their indices
    cities = ['Dublin', 'Madrid', 'Oslo', 'London', 'Vilnius', 'Berlin']
    required_days = [3, 2, 3, 2, 3, 5]
    
    # Direct flights (as city index pairs)
    direct_flights = [(1, 3), (2, 4), (4, 5), (1, 2), (1, 0), (3, 2), (1, 5), (5, 2), (0, 2), (3, 0), (3, 5), (5, 0)]
    allowed_edges = []
    for a, b in direct_flights:
        allowed_edges.append((a, b))
        allowed_edges.append((b, a))
    
    # Z3 variables
    order = [Int(f'order_{i}') for i in range(6)]
    start = [Int(f'start_{i}') for i in range(6)]
    end = [Int(f'end_{i}') for i in range(6)]
    
    solver = Solver()
    
    # Domain constraints for order
    for i in range(6):
        solver.add(And(0 <= order[i], order[i] <= 5))
    solver.add(Distinct(order))
    
    # Domain constraints for start and end
    for i in range(6):
        solver.add(And(1 <= start[i], start[i] <= 13))
        solver.add(And(1 <= end[i], end[i] <= 13))
    
    # City day constraints
    for i in range(6):
        solver.add(end[i] - start[i] + 1 == required_days[i])
    
    # First and last city constraints
    first_city_constraints = []
    for j in range(6):
        first_city_constraints.append(And(order[0] == j, start[j] == 1))
    solver.add(Or(first_city_constraints))
    
    last_city_constraints = []
    for j in range(6):
        last_city_constraints.append(And(order[5] == j, end[j] == 13))
    solver.add(Or(last_city_constraints))
    
    # Travel day constraints
    for i in range(5):
        step_constraints = []
        for j in range(6):
            for k in range(6):
                step_constraints.append(And(order[i] == j, order[i+1] == k, end[j] == start[k]))
        solver.add(Or(step_constraints))
    
    # Flight constraints
    for i in range(5):
        flight_constraints = []
        for a, b in allowed_edges:
            flight_constraints.append(And(order[i] == a, order[i+1] == b))
        solver.add(Or(flight_constraints))
    
    # Specific city constraints
    solver.add(start[0] <= 9, end[0] >= 7)  # Dublin
    solver.add(start[1] <= 3, end[1] >= 2)  # Madrid
    solver.add(start[5] <= 7, end[5] >= 3)  # Berlin
    
    # Check solution
    if solver.check() == sat:
        model = solver.model()
        order_values = [model.evaluate(order[i]) for i in range(6)]
        itinerary_segments = []
        for i in range(6):
            city_idx = order_values[i].as_long()
            s_val = model.evaluate(start[city_idx]).as_long()
            e_val = model.evaluate(end[city_idx]).as_long()
            itinerary_segments.append({
                "day_range": f"Day {s_val}-{e_val}",
                "place": cities[city_idx]
            })
        result = {"itinerary": itinerary_segments}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()