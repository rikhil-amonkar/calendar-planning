from z3 import *

def main():
    cities = ['Porto', 'Prague', 'Reykjavik', 'Santorini', 'Amsterdam', 'Munich']
    required_days = [5, 4, 4, 2, 2, 4]  # in the order of the cities list
    allowed_edges = [
        (0, 4), (5, 4), (2, 4), (5, 0), 
        (1, 2), (2, 5), (4, 3), (1, 4), (1, 5)
    ]
    
    # Create the solver
    s = Solver()
    
    # Position variables: the city index at each sequence position
    pos = [Int('pos_%d' % i) for i in range(6)]
    # Arrival and departure days for each position
    arr = [Int('arr_%d' % i) for i in range(6)]
    dep = [Int('dep_%d' % i) for i in range(6)]
    
    # Constraints for pos: each is between 0 and 5, and all distinct
    for i in range(6):
        s.add(pos[i] >= 0, pos[i] <= 5)
    s.add(Distinct(pos))
    
    # Trip constraints: start at day 1, end at day 16
    s.add(arr[0] == 1)
    s.add(dep[5] == 16)
    
    # For consecutive cities: departure from i equals arrival at i+1
    for i in range(5):
        s.add(dep[i] == arr[i+1])
    
    # Stay at each city must be at least one day
    for i in range(6):
        s.add(dep[i] >= arr[i])
    
    # Flight constraints: consecutive cities must have a direct flight
    for i in range(5):
        edge_constraints = []
        for (a, b) in allowed_edges:
            # Either (current city is a and next is b) or (current is b and next is a)
            edge_constraints.append(And(pos[i] == a, pos[i+1] == b))
            edge_constraints.append(And(pos[i] == b, pos[i+1] == a))
        s.add(Or(edge_constraints))
    
    # Required days per city: for each city c, the stay where it appears must be required_days[c]
    for c in range(6):
        total_days = 0
        for j in range(6):
            total_days += If(pos[j] == c, dep[j] - arr[j] + 1, 0)
        s.add(total_days == required_days[c])
    
    # Event constraints
    # Reykjavik is city 2: must have at least one day in [4,7]
    for j in range(6):
        s.add(If(pos[j] == 2, And(arr[j] <= 7, dep[j] >= 4), True))
    
    # Amsterdam is city 4: must be present on day14 and day15
    for j in range(6):
        s.add(If(pos[j] == 4, And(arr[j] <= 14, dep[j] >= 15), True))
    
    # Munich is city 5: must have at least one day in [7,10]
    for j in range(6):
        s.add(If(pos[j] == 5, And(arr[j] <= 10, dep[j] >= 7), True))
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        pos_vals = [m.evaluate(pos[i]).as_long() for i in range(6)]
        arr_vals = [m.evaluate(arr[i]).as_long() for i in range(6)]
        dep_vals = [m.evaluate(dep[i]).as_long() for i in range(6)]
        
        # Build the itinerary
        itinerary = []
        for j in range(6):
            city_name = cities[pos_vals[j]]
            # Entire stay record for the city
            itinerary.append({
                "day_range": f"Day {arr_vals[j]}-{dep_vals[j]}",
                "place": city_name
            })
            # If not the last city, add departure and next city's arrival records
            if j < 5:
                # Departure record for current city on flight day
                itinerary.append({
                    "day_range": f"Day {dep_vals[j]}",
                    "place": city_name
                })
                # Arrival record for next city on the same flight day
                next_city_name = cities[pos_vals[j+1]]
                itinerary.append({
                    "day_range": f"Day {arr_vals[j+1]}",
                    "place": next_city_name
                })
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()