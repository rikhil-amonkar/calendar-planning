from z3 import *

def main():
    cities = ['Berlin', 'Milan', 'Seville', 'Paris', 'Lyon', 'Nice', 'Naples', 'Zurich', 'Stockholm', 'Riga']
    n = len(cities)
    num_days = 23
    
    # Create Z3 variables for start and end days of each city
    start_vars = {city: Int(f'start_{city}') for city in cities}
    end_vars = {city: Int(f'end_{city}') for city in cities}
    
    # Create ordering variables: a permutation of [0, n-1]
    order = [Int(f'order_{i}') for i in range(n)]
    
    s = Solver()
    
    # Each city must have a duration of at least 2 days
    for city in cities:
        s.add(start_vars[city] >= 1)
        s.add(end_vars[city] <= num_days)
        s.add(end_vars[city] - start_vars[city] + 1 >= 2)
    
    # Order variables must be in [0, n-1] and distinct
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))
    
    # Create sorted start and end arrays based on the order
    sorted_start = [Int(f'sorted_start_{i}') for i in range(n)]
    sorted_end = [Int(f'sorted_end_{i}') for i in range(n)]
    
    # Link order to city start/end variables
    for i in range(n):
        # sorted_start[i] must equal start_vars[city] for the city at position i in the order
        s.add(Or([And(order[i] == idx, sorted_start[i] == start_vars[city]) for idx, city in enumerate(cities)]))
        # sorted_end[i] must equal end_vars[city] for the city at position i in the order
        s.add(Or([And(order[i] == idx, sorted_end[i] == end_vars[city]) for idx, city in enumerate(cities)]))
    
    # First city in order starts at day 1
    s.add(sorted_start[0] == 1)
    # Last city in order ends at day 23
    s.add(sorted_end[n-1] == num_days)
    # Consecutive cities: end[i] + 1 = start[i+1]
    for i in range(n-1):
        s.add(sorted_end[i] + 1 == sorted_start[i+1])
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        # Extract the order of cities
        order_vals = []
        for i in range(n):
            order_vals.append(model.eval(order[i]).as_long())
        
        # Get cities in the determined order
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