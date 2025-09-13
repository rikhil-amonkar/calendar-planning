import z3
import json

def main():
    # Define cities and their durations
    durations = [5, 4, 5, 2, 3, 5]  # [Reykjavik, Istanbul, Edinburgh, Oslo, Stuttgart, Bucharest]
    city_names = ['Reykjavik', 'Istanbul', 'Edinburgh', 'Oslo', 'Stuttgart', 'Bucharest']
    
    # Define allowed transitions matrix
    allowed = [
        [False, True, False, True, True, True],   # Reykjavik (0)
        [True, False, True, True, True, True],    # Istanbul (1)
        [False, True, False, True, True, False],  # Edinburgh (2)
        [True, True, True, False, False, True],   # Oslo (3)
        [True, True, True, False, False, False],  # Stuttgart (4)
        [True, True, False, True, False, False],  # Bucharest (5)
    ]
    
    # Generate allowed_pairs
    allowed_pairs = []
    for i in range(6):
        for j in range(6):
            if allowed[i][j]:
                allowed_pairs.append((i, j))
    
    # Create Z3 solver
    s = z3.Solver()
    
    # Variables for order of cities (each is 0-5, all distinct)
    order = [z3.Int(f'pos_{i}') for i in range(6)]
    
    # Constraints: order is a permutation of 0-5
    for i in range(6):
        s.add(order[i] >= 0, order[i] <= 5)
    s.add(z3.Distinct(order))
    
    # Constraints for allowed transitions between consecutive cities
    for i in range(5):  # 0 to 4
        a = order[i]
        b = order[i+1]
        constraints = []
        for (x, y) in allowed_pairs:
            constraints.append(z3.And(a == x, b == y))
        s.add(z3.Or(*constraints))
    
    # Variables for cumulative sum of durations
    cum_sum = [z3.Int(f'cum_sum_{i}') for i in range(6)]
    s.add(cum_sum[0] == 0)
    for i in range(1, 6):
        s.add(cum_sum[i] == cum_sum[i-1] + durations[order[i-1]])
    
    # Constraints for Istanbul's start day (must be 5)
    for i in range(6):
        start_day = 1 + cum_sum[i]
        s.add(z3.Implies(order[i] == 1, start_day == 5))
    
    # Constraints for Oslo's start day (must be between 7 and 9 inclusive)
    for i in range(6):
        start_day = 1 + cum_sum[i]
        s.add(z3.Implies(order[i] == 3, z3.And(7 <= start_day, start_day <= 9)))
    
    # Check if the constraints are satisfiable
    if s.check() == z3.sat:
        model = s.model()
        # Extract the order
        order_values = [model.evaluate(order[i]).as_long() for i in range(6)]
        # Extract cum_sum values
        cum_sum_values = [model.evaluate(cum_sum[i]).as_long() for i in range(6)]
        
        # Build the itinerary
        itinerary = []
        for i in range(6):
            city_idx = order_values[i]
            city_name = city_names[city_idx]
            start_day = 1 + cum_sum_values[i]
            duration = durations[city_idx]
            end_day = start_day + duration - 1
            day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": city_name})
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()