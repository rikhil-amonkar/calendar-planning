from z3 import *

def main():
    cities = ['Berlin', 'Milan', 'Seville', 'Paris', 'Lyon', 'Nice', 'Naples', 'Zurich', 'Stockholm', 'Riga']
    n = len(cities)
    
    # Create Z3 variables for start and end days of each city
    start_vars = {city: Int(f'start_{city}') for city in cities}
    end_vars = {city: Int(f'end_{city}') for city in cities}
    
    # Create ordering variables: a permutation of [0, n-1]
    order = [Int(f'order_{i}') for i in range(n)]
    
    s = Solver()
    
    # Each city must have a duration of at least 2 days
    for city in cities:
        s.add(start_vars[city] >= 1)
        s.add(end_vars[city] <= 23)
        s.add(end_vars[city] - start_vars[city] + 1 >= 2)
    
    # Order variables must be in [0, n-1] and distinct
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))
    
    # Create sorted start and end arrays based on the order
    sorted_start = [Int(f'sorted_start_{i}') for i in range(n)]
    sorted_end = [Int(f'sorted_end_{i}') for i in range(n)]
    
    # For each position in the order, link to the corresponding city's start and end
    for i in range(n):
        expr_start = None
        expr_end = None
        for idx, city in enumerate(cities):
            if expr_start is None:
                expr_start = If(order[i] == idx, start_vars[city], IntVal(0))
                expr_end = If(order[i] == idx, end_vars[city], IntVal(0))
            else:
                expr_start = If(order[i] == idx, start_vars[city], expr_start)
                expr_end = If(order[i] == idx, end_vars[city], expr_end)
        s.add(sorted_start[i] == expr_start)
        s.add(sorted_end[i] == expr_end)
    
    # The first city in the order must start on day 1
    s.add(sorted_start[0] == 1)
    # The last city in the order must end on day 23
    s.add(sorted_end[n-1] == 23)
    
    # Consecutive cities in the order must be contiguous: end[i] + 1 = start[i+1]
    for i in range(n-1):
        s.add(sorted_end[i] + 1 == sorted_start[i+1])
    
    # Total days must sum to 23
    total_days = Int('total_days')
    s.add(total_days == Sum([end_vars[city] - start_vars[city] + 1 for city in cities]))
    s.add(total_days == 23)
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        # Extract the order of cities
        order_vals = []
        for i in range(n):
            order_val = model.eval(order[i]).as_long()
            order_vals.append(order_val)
        
        # Get the cities in the determined order
        ordered_cities = [cities[idx] for idx in order_vals]
        
        # Build itinerary with start and end days
        itinerary = []
        for city in ordered_cities:
            s_val = model.eval(start_vars[city]).as_long()
            e_val = model.eval(end_vars[city]).as_long()
            day_range = f"Day {s_val}-{e_val}"
            itinerary.append({'day_range': day_range, 'place': city})
        
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found.")

if __name__ == '__main__':
    main()