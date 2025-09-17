from z3 import *
import json

def main():
    # Cities and their required days
    cities = ['Salzburg', 'Stockholm', 'Venice', 'Frankfurt', 'Florence', 'Barcelona', 'Stuttgart']
    req_days = {
        'Salzburg': 4,
        'Stockholm': 2,
        'Venice': 5,
        'Frankfurt': 4,
        'Florence': 4,
        'Barcelona': 2,
        'Stuttgart': 3
    }
    
    # Direct flight connections (undirected)
    connections = [
        ('Barcelona', 'Frankfurt'),
        ('Florence', 'Frankfurt'),
        ('Stockholm', 'Barcelona'),
        ('Barcelona', 'Florence'),
        ('Venice', 'Barcelona'),
        ('Stuttgart', 'Barcelona'),
        ('Frankfurt', 'Salzburg'),
        ('Stockholm', 'Frankfurt'),
        ('Stuttgart', 'Stockholm'),
        ('Stuttgart', 'Frankfurt'),
        ('Venice', 'Stuttgart'),
        ('Venice', 'Frankfurt')
    ]
    
    # Map city names to indices
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    idx_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Create graph of connections using indices
    graph = set()
    for conn in connections:
        i1 = city_to_idx[conn[0]]
        i2 = city_to_idx[conn[1]]
        graph.add((i1, i2))
        graph.add((i2, i1))
    
    # Z3 variables
    n_cities = len(cities)
    total_days = 18
    
    # Use arrays for starts and ends to allow Z3 variable indexing
    starts_array = Array('starts', IntSort(), IntSort())
    ends_array = Array('ends', IntSort(), IntSort())
    
    # Order of cities visited (permutation)
    order = [Int(f'order_{i}') for i in range(n_cities)]
    
    solver = Solver()
    
    # Define starts and ends for each city
    for i in range(n_cities):
        solver.add(starts_array[i] >= 1)
        solver.add(ends_array[i] <= total_days)
        solver.add(ends_array[i] - starts_array[i] + 1 == req_days[idx_to_city[i]])
    
    # Venice must be visited from day 1 to 5
    venice_idx = city_to_idx['Venice']
    solver.add(starts_array[venice_idx] == 1)
    solver.add(ends_array[venice_idx] == 5)
    
    # Order is a permutation of cities
    solver.add(Distinct(order))
    for i in range(n_cities):
        solver.add(order[i] >= 0)
        solver.add(order[i] < n_cities)
    
    # The first city in order must be Venice (since it starts on day 1)
    solver.add(order[0] == venice_idx)
    
    # Constraints for consecutive cities in order
    for i in range(n_cities - 1):
        city_i = order[i]
        city_j = order[i+1]
        # The end day of city_i equals the start day of city_j (travel day)
        solver.add(ends_array[city_i] == starts_array[city_j])
        # There must be a direct flight between city_i and city_j
        solver.add(Or(*[And(city_i == a, city_j == b) for (a, b) in graph]))
    
    # The trip must end at day 18
    solver.add(ends_array[order[n_cities-1]] == total_days)
    
    # Check satisfiability
    if solver.check() == sat:
        model = solver.model()
        # Extract the order of cities
        visit_order = []
        for i in range(n_cities):
            idx = model.evaluate(order[i]).as_long()
            visit_order.append(idx)
        
        # Extract start and end days for each city in the order
        itinerary = []
        for idx in visit_order:
            start_val = model.evaluate(starts_array[idx]).as_long()
            end_val = model.evaluate(ends_array[idx]).as_long()
            itinerary.append({
                'day_range': f"Day {start_val}-{end_val}",
                'place': idx_to_city[idx]
            })
        
        # Output as JSON
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print('No valid itinerary found')

if __name__ == '__main__':
    main()