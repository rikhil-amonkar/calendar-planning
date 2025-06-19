from z3 import *

def main():
    # City indices
    cities = ["Prague", "Tallinn", "Warsaw", "Porto", "Naples", "Milan", "Lisbon", "Santorini", "Riga", "Stockholm"]
    days_list = [5, 3, 2, 3, 5, 3, 5, 5, 4, 2]  # days required for each city

    # Build directed flight graph
    allowed_edges = set()
    # Helper function to add bidirectional edges
    def add_bidirectional(a, b):
        allowed_edges.add((a, b))
        allowed_edges.add((b, a))
    
    # Add edges as per the problem description
    add_bidirectional(8, 0)    # Riga and Prague
    add_bidirectional(9, 5)    # Stockholm and Milan
    add_bidirectional(8, 5)    # Riga and Milan
    add_bidirectional(6, 9)    # Lisbon and Stockholm
    allowed_edges.add((9, 7))   # from Stockholm to Santorini (unidirectional)
    add_bidirectional(4, 2)    # Naples and Warsaw
    add_bidirectional(6, 2)    # Lisbon and Warsaw
    add_bidirectional(4, 5)    # Naples and Milan
    add_bidirectional(6, 4)    # Lisbon and Naples
    allowed_edges.add((8, 1))   # from Riga to Tallinn (unidirectional)
    add_bidirectional(1, 0)    # Tallinn and Prague
    add_bidirectional(9, 2)    # Stockholm and Warsaw
    add_bidirectional(8, 2)    # Riga and Warsaw
    add_bidirectional(6, 8)    # Lisbon and Riga
    add_bidirectional(8, 9)    # Riga and Stockholm
    add_bidirectional(6, 3)    # Lisbon and Porto
    add_bidirectional(6, 0)    # Lisbon and Prague
    add_bidirectional(5, 3)    # Milan and Porto
    add_bidirectional(0, 5)    # Prague and Milan
    add_bidirectional(6, 5)    # Lisbon and Milan
    add_bidirectional(2, 3)    # Warsaw and Porto
    add_bidirectional(2, 1)    # Warsaw and Tallinn
    add_bidirectional(7, 5)    # Santorini and Milan
    add_bidirectional(9, 0)    # Stockholm and Prague
    add_bidirectional(9, 1)    # Stockholm and Tallinn
    add_bidirectional(2, 5)    # Warsaw and Milan
    add_bidirectional(7, 4)    # Santorini and Naples
    add_bidirectional(2, 0)    # Warsaw and Prague

    # Initialize Z3 solver
    s = Solver()
    
    # Order and start day variables
    order = [Int(f"order_{i}") for i in range(10)]
    start = [Int(f"start_{i}") for i in range(10)]
    
    # Create a Z3 array for durations
    durations = Array('durations', IntSort(), IntSort())
    for j in range(10):
        s.add(durations[j] == days_list[j])
    
    # Constraints: order is a permutation of 0-9
    s.add(Distinct(order))
    for i in range(10):
        s.add(order[i] >= 0, order[i] < 10)
    
    # Start day constraints
    s.add(start[0] == 1)  # First city starts on day 1
    for i in range(9):
        # Start of next city = start of current + duration of current city - 1
        s.add(start[i+1] == start[i] + Select(durations, order[i]) - 1)
    # Total trip ends by day 28
    s.add(start[9] + Select(durations, order[9]) - 1 <= 28)
    
    # Flight constraints: consecutive cities must have a direct flight
    for i in range(9):
        constraints = []
        for (a, b) in allowed_edges:
            constraints.append(And(order[i] == a, order[i+1] == b))
        s.add(Or(constraints))
    
    # City-specific constraints
    # Riga (index 8): at least one day between 5-8
    # Tallinn (index 1): at least one day between 18-20
    # Milan (index 5): at least one day between 24-26
    for j in range(10):
        s.add(If(order[j] == 8, And(start[j] <= 8, start[j] + 3 >= 5), True))
        s.add(If(order[j] == 1, And(start[j] >= 18, start[j] <= 20), True))
        s.add(If(order[j] == 5, And(start[j] >= 22, start[j] <= 26), True))
    
    # Check and get solution
    if s.check() == sat:
        model = s.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(10)]
        start_val = [model.evaluate(start[i]).as_long() for i in range(10)]
        
        # Print the trip plan
        print("Trip Plan:")
        for i in range(10):
            city_idx = order_val[i]
            city_name = cities[city_idx]
            start_day = start_val[i]
            end_day = start_day + days_list[city_idx] - 1
            print(f"City: {city_name}, Start Day: {start_day}, End Day: {end_day}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()