from z3 import *

def main():
    # List of cities to visit
    cities = ["Tallinn", "Munich", "Venice", "Santorini", "Manchester", "Porto", "Valencia", "Bucharest", "Vienna", "Reykjavik"]
    
    # Flight connections (direct flights) - include only cities in our itinerary
    flight_connections = {
        "Tallinn": ["Munich"],
        "Munich": ["Tallinn", "Venice", "Vienna", "Manchester"],
        "Venice": ["Munich", "Santorini", "Porto", "Valencia"],
        "Santorini": ["Venice", "Porto", "Valencia"],
        "Manchester": ["Munich", "Reykjavik"],
        "Porto": ["Venice", "Santorini", "Valencia"],
        "Valencia": ["Venice", "Santorini", "Porto"],
        "Bucharest": ["Vienna"],
        "Vienna": ["Munich", "Bucharest"],
        "Reykjavik": ["Manchester"]
    }
    
    num_cities = len(cities)
    total_days = 24
    christmas_eve = 23  # December 24 is day 23 (0-indexed from December 1)
    
    # Create Z3 sorts and constants for cities
    City, city_consts = EnumSort('City', cities)
    city_dict = {name: const for name, const in zip(cities, city_consts)}
    
    # Convert flight_connections to use Z3 constants (only include cities in itinerary)
    flight_connections_const = {}
    for city_str, neighbors in flight_connections.items():
        # Filter neighbors to only cities in our itinerary
        valid_neighbors = [n for n in neighbors if n in cities]
        c = city_dict[city_str]
        n_list = [city_dict[n] for n in valid_neighbors]
        flight_connections_const[c] = n_list
    
    # Precompute allowed edges for flight constraints
    allowed_edges = []
    for c, neighbors in flight_connections_const.items():
        for n in neighbors:
            allowed_edges.append((c, n))
    
    # Initialize Z3 solver
    solver = Solver()
    
    # Itinerary: sequence of cities
    itinerary = [Const(f"itinerary_{i}", City) for i in range(num_cities)]
    # Durations: days spent in each city
    duration = [Int(f"duration_{i}") for i in range(num_cities)]
    # Start day for each city visit
    start_day = [Int(f"start_{i}") for i in range(num_cities)]
    
    # Constraint: each city appears exactly once in the itinerary
    solver.add(Distinct(itinerary))
    
    # Constraint: total days must sum to 24
    solver.add(sum(duration) == total_days)
    
    # Constraint: minimum 2 days per city except last city can be 1
    for i in range(num_cities - 1):
        solver.add(duration[i] >= 2)
    solver.add(duration[num_cities - 1] >= 1)
    
    # Constraints for start days
    solver.add(start_day[0] == 0)
    for i in range(num_cities - 1):
        solver.add(start_day[i + 1] == start_day[i] + duration[i])
    solver.add(start_day[num_cities - 1] + duration[num_cities - 1] == total_days)
    
    # Flight constraints between consecutive cities
    for i in range(num_cities - 1):
        from_city = itinerary[i]
        to_city = itinerary[i + 1]
        solver.add(Or([And(from_city == edge[0], to_city == edge[1]) for edge in allowed_edges]))
    
    # Constraint: Vienna must include Christmas Eve (day 23)
    vienna = city_dict["Vienna"]
    vienna_constraints = []
    for i in range(num_cities):
        # Check if the current city in the itinerary is Vienna and day 23 falls within its duration
        in_vienna = And(
            itinerary[i] == vienna,
            start_day[i] <= christmas_eve,
            christmas_eve < start_day[i] + duration[i]
        )
        vienna_constraints.append(in_vienna)
    solver.add(Or(vienna_constraints))
    
    # Check if a solution exists
    if solver.check() == sat:
        model = solver.model()
        # Extract the itinerary and durations
        itinerary_vals = [model.eval(itinerary[i]) for i in range(num_cities)]
        duration_vals = [model.eval(duration[i]).as_long() for i in range(num_cities)]
        
        # Calculate start and end days for each city
        start_day_vals = [0] * num_cities
        if num_cities > 0:
            start_day_vals[0] = 0
            for i in range(1, num_cities):
                start_day_vals[i] = start_day_vals[i-1] + duration_vals[i-1]
        
        # Format the itinerary with day ranges
        result = []
        for i in range(num_cities):
            start = start_day_vals[i]
            end = start + duration_vals[i] - 1
            if start == end:
                day_range = f"Day {start+1}"
            else:
                day_range = f"Day {start+1}-{end+1}"
            city_name = cities[city_consts.index(itinerary_vals[i])]
            result.append({'day_range': day_range, 'place': city_name})
        
        plan = {'itinerary': result}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()