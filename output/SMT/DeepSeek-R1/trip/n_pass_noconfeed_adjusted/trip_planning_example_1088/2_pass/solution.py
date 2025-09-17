import z3
import json

def main():
    # Define city names and their required days
    city_names = ['Reykjavik', 'Oslo', 'Stockholm', 'Tallinn', 'Geneva', 'Porto', 'Stuttgart', 'Split']
    required_days = [2, 5, 3, 5, 2, 3, 5, 3]
    
    # Map city names to indices
    city_index = {city: idx for idx, city in enumerate(city_names)}
    
    # Define direct flights as tuples of city indices
    flight_pairs = [
        ('Reykjavik', 'Stuttgart'), ('Reykjavik', 'Stockholm'), ('Reykjavik', 'Tallinn'),
        ('Stockholm', 'Oslo'), ('Stuttgart', 'Porto'), ('Oslo', 'Split'),
        ('Stockholm', 'Stuttgart'), ('Reykjavik', 'Oslo'), ('Oslo', 'Geneva'),
        ('Stockholm', 'Split'), ('Reykjavik', 'Stockholm'), ('Split', 'Stuttgart'),
        ('Tallinn', 'Oslo'), ('Stockholm', 'Geneva'), ('Oslo', 'Porto'),
        ('Geneva', 'Porto'), ('Geneva', 'Split')
    ]
    
    # Create set of allowed connections (both directions)
    allowed_connections = set()
    for city1, city2 in flight_pairs:
        idx1 = city_index[city1]
        idx2 = city_index[city2]
        allowed_connections.add((idx1, idx2))
        allowed_connections.add((idx2, idx1))
    
    # Initialize Z3 solver
    solver = z3.Solver()
    
    # Define order variables: 8 integers representing the city index at each segment
    order = [z3.Int(f'order_{i}') for i in range(8)]
    
    # Constraint: each order variable is between 0 and 7
    for o in order:
        solver.add(z3.And(o >= 0, o <= 7))
    
    # Constraint: all order variables are distinct
    solver.add(z3.Distinct(order))
    
    # Fix first city to Reykjavik (index 0)
    solver.add(order[0] == city_index['Reykjavik'])
    
    # Define start and end days for each segment
    start = [z3.Int(f'start_{i}') for i in range(8)]
    end = [z3.Int(f'end_{i}') for i in range(8)]
    
    # Helper function to get required days using Z3 expressions
    def get_req_days(idx):
        cases = []
        for i in range(8):
            cases.append((idx == i, required_days[i]))
        return z3.If(*cases[0], *[(cond, res) for cond, res in cases[1:]])
    
    # Constraint for first segment
    solver.add(start[0] == 1)
    solver.add(end[0] == start[0] + get_req_days(order[0]) - 1)
    
    # Constraints for subsequent segments
    for i in range(1, 8):
        solver.add(start[i] == end[i-1])
        solver.add(end[i] == start[i] + get_req_days(order[i]) - 1)
    
    # Constraint: total trip ends at day 21
    solver.add(end[7] == 21)
    
    # Constraint: Porto must start on day 19
    porto_idx = city_index['Porto']
    for i in range(8):
        solver.add(z3.Implies(order[i] == porto_idx, start[i] == 19))
    
    # Constraint: Stockholm must start on or before day 4
    stockholm_idx = city_index['Stockholm']
    for i in range(8):
        solver.add(z3.Implies(order[i] == stockholm_idx, start[i] <= 4))
    
    # Constraints for direct flights between consecutive cities
    for i in range(1, 8):
        solver.add(z3.Or([z3.And(order[i-1] == idx1, order[i] == idx2) for (idx1, idx2) in allowed_connections]))
    
    # Check if the problem is satisfiable
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Extract the order of cities
        itinerary_order = [model.evaluate(order[i]).as_long() for i in range(8)]
        
        # Extract start and end days
        start_days = [model.evaluate(start[i]).as_long() for i in range(8)]
        end_days = [model.evaluate(end[i]).as_long() for i in range(8)]
        
        # Build itinerary list
        itinerary = []
        for i in range(8):
            city = city_names[itinerary_order[i]]
            day_range = f"Day {start_days[i]}-{end_days[i]}"
            itinerary.append({"day_range": day_range, "place": city})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()