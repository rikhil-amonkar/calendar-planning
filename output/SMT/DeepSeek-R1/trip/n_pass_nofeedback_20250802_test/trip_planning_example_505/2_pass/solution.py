from z3 import *

def main():
    s = Solver()
    n_days = 7
    city_names = {0: 'Krakow', 1: 'Stuttgart', 2: 'Split', 3: 'Prague', 4: 'Florence'}
    n_cities = len(city_names)
    
    # Create variables for each day
    X = [Int('x_%d' % i) for i in range(n_days)]
    
    # Each X[i] must be between 0 and 4
    for i in range(n_days):
        s.add(X[i] >= 0, X[i] < n_cities)
    
    # Start and end in Krakow (0)
    s.add(X[0] == 0)
    s.add(X[6] == 0)
    
    # Define allowed edges (undirected)
    edges_list = [
        (0, 1), (0, 3), 
        (1, 2), (1, 3), 
        (3, 4), (0, 4), 
        (2, 3), (2, 4)
    ]
    allowed_pairs = set()
    # Add stay moves (same city)
    for c in range(n_cities):
        allowed_pairs.add((c, c))
    # Add travel moves in both directions
    for (u, v) in edges_list:
        allowed_pairs.add((u, v))
        allowed_pairs.add((v, u))
    allowed_pairs = list(allowed_pairs)
    
    # Add constraints for consecutive days
    for i in range(n_days - 1):
        options = []
        for (a, b) in allowed_pairs:
            options.append(And(X[i] == a, X[i+1] == b))
        s.add(Or(options))
    
    # Each non-Krakow city must appear at least once
    for city in range(1, n_cities):
        s.add(Or([X[i] == city for i in range(n_days)]))
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        res = [m.evaluate(X[i]).as_long() for i in range(n_days)]
        itinerary = []
        for i in range(n_days):
            itinerary.append({'day_range': f'Day {i+1}-{i+1}', 'place': city_names[res[i]]})
        print(f"Plan found: {itinerary}")
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()