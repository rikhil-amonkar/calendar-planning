import z3

def main():
    cities = ["Mykonos", "Naples", "Venice", "Istanbul", "Dublin", "Brussels", "Frankfurt", "Krakow"]
    n_cities = len(cities)
    
    # Flight matrix: 1 indicates a direct flight exists
    flights = [
        [0, 1, 1, 1, 1, 0, 0, 0],  # Mykonos (0)
        [1, 0, 1, 0, 0, 0, 1, 0],  # Naples (1)
        [1, 1, 0, 1, 0, 0, 1, 1],  # Venice (2)
        [1, 0, 1, 0, 1, 0, 1, 0],  # Istanbul (3)
        [1, 0, 0, 1, 0, 1, 1, 0],  # Dublin (4)
        [0, 0, 0, 0, 1, 0, 1, 1],  # Brussels (5)
        [0, 1, 1, 1, 1, 1, 0, 1],  # Frankfurt (6)
        [0, 0, 1, 0, 0, 1, 1, 0]   # Krakow (7)
    ]
    
    allowed_set = set()
    for a in range(n_cities):
        for b in range(n_cities):
            if flights[a][b] == 1:
                allowed_set.add((a, b))
    
    # Z3 variables
    order = [z3.Int(f"order_{i}") for i in range(n_cities)]
    stays = [z3.Int(f"stay_{i}") for i in range(n_cities)]
    
    solver = z3.Solver()
    
    # Order constraints
    for i in range(n_cities):
        solver.add(order[i] >= 0, order[i] < n_cities)
    solver.add(z3.Distinct(order))
    solver.add(order[0] == 0)
    solver.add(order[7] == 7)
    
    # Stay constraints
    for i in range(n_cities):
        solver.add(stays[i] >= 2)
    solver.add(sum(stays) == 21)
    
    # Flight constraints
    for i in range(n_cities - 1):
        constraints = [z3.And(order[i] == a, order[i+1] == b) for (a, b) in allowed_set]
        solver.add(z3.Or(constraints))
    
    if solver.check() == z3.sat:
        model = solver.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(n_cities)]
        stays_val = [model.evaluate(stays[i]).as_long() for i in range(n_cities)]
        
        itinerary = []
        current_day = 1
        for i in range(n_cities):
            end_day = current_day + stays_val[i] - 1
            day_range = f"Day {current_day}-{end_day}" if stays_val[i] > 1 else f"Day {current_day}"
            itinerary.append({
                'day_range': day_range,
                'place': cities[order_val[i]]
            })
            current_day = end_day + 1
        
        print("Plan found:", {'itinerary': itinerary})
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()