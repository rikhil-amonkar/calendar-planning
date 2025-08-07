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
    
    # Define allowed edges (undirected) including self-loops
    allowed_pairs = []
    # Add self-loops (staying in same city)
    for c in range(n_cities):
        allowed_pairs.append((c, c))
    # Add travel moves
    edges = [(0, 1), (0, 3), (0, 4), 
             (1, 2), (1, 3), 
             (2, 3), (2, 4),
             (3, 4)]
    for (u, v) in edges:
        allowed_pairs.append((u, v))
        allowed_pairs.append((v, u))
    
    # Add constraints for consecutive days
    for i in range(n_days - 1):
        s.add(Or([And(X[i] == u, X[i+1] == v) for (u, v) in allowed_pairs]))
    
    # Each non-Krakow city has at least one pair of consecutive days
    for city in range(1, n_cities):
        consec_days = []
        for i in range(n_days - 1):
            consec_days.append(And(X[i] == city, X[i+1] == city))
        s.add(Or(consec_days))
    
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