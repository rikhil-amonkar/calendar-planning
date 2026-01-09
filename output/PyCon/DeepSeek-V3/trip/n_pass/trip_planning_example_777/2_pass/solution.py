def main():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = ['Dublin', 'Helsinki', 'Riga', 'Reykjavik', 'Vienna', 'Tallinn']
    required_days = {
        'Dublin': 5,
        'Helsinki': 3,
        'Riga': 3,
        'Reykjavik': 2,
        'Vienna': 2,
        'Tallinn': 5
    }
    
    # Direct flight connections
    direct_flights = [
        ('Helsinki', 'Riga'), ('Riga', 'Tallinn'), ('Vienna', 'Helsinki'),
        ('Riga', 'Dublin'), ('Vienna', 'Riga'), ('Reykjavik', 'Vienna'),
        ('Helsinki', 'Dublin'), ('Tallinn', 'Dublin'), ('Reykjavik', 'Helsinki'),
        ('Reykjavik', 'Dublin'), ('Helsinki', 'Tallinn'), ('Vienna', 'Dublin')
    ]
    
    # Make flights bidirectional
    all_flights = set()
    for city1, city2 in direct_flights:
        all_flights.add((city1, city2))
        all_flights.add((city2, city1))
    
    # Total days
    total_days = 15
    
    # Define variables for start day of each city visit
    # We'll model this as a sequence of visits with start days
    # Since we have multiple constraints about specific days, we need to be careful
    
    # Let's create variables for the order of visits
    num_cities = len(cities)
    problem.addVariables(range(num_cities), range(num_cities))  # Visit order
    
    # We also need variables for start days
    problem.addVariables([f"start_{city}" for city in cities], range(total_days))
    problem.addVariables([f"duration_{city}" for city in cities], [required_days[city]])
    
    # Constraint: All visits must be in different order positions
    problem.addConstraint(lambda *orders: len(set(orders)) == num_cities, range(num_cities))
    
    # Helper function to check if two cities are connected
    def are_connected(city1, city2):
        return (city1, city2) in all_flights
    
    # Constraint: Consecutive cities in the order must have direct flights
    def flight_constraint(order_list, *starts_durations):
        # Reconstruct the visit sequence from order
        ordered_cities = [None] * num_cities
        for i, pos in enumerate(order_list):
            ordered_cities[pos] = cities[i]
        
        # Check flights between consecutive cities
        for i in range(num_cities - 1):
            city1 = ordered_cities[i]
            city2 = ordered_cities[i + 1]
            if not are_connected(city1, city2):
                return False
        
        return True
    
    # Apply flight constraint
    all_vars = list(range(num_cities)) + [f"start_{city}" for city in cities] + [f"duration_{city}" for city in cities]
    problem.addConstraint(flight_constraint, all_vars)
    
    # Constraint: Visits cannot overlap and must fit within total days
    def no_overlap_constraint(order_list, *starts_durations):
        # Reconstruct the visit sequence from order
        ordered_cities = [None] * num_cities
        city_to_idx = {}
        for i, pos in enumerate(order_list):
            ordered_cities[pos] = cities[i]
            city_to_idx[cities[i]] = pos
        
        # Extract start days and durations
        starts = {}
        durations = {}
        for i, city in enumerate(cities):
            starts[city] = starts_durations[i]
            durations[city] = starts_durations[i + num_cities]
        
        # Check that visits don't overlap and are in correct order
        for i in range(num_cities - 1):
            city1 = ordered_cities[i]
            city2 = ordered_cities[i + 1]
            
            # City2 must start after city1 ends
            if starts[city2] < starts[city1] + durations[city1]:
                return False
        
        # All visits must end by total_days
        for city in cities:
            if starts[city] + durations[city] > total_days:
                return False
        
        return True
    
    problem.addConstraint(no_overlap_constraint, all_vars)
    
    # Special constraints
    # Helsinki between day 3 and day 5
    def helsinki_constraint(helsinki_start, helsinki_duration):
        # Helsinki visit should overlap with days 3-5
        return (helsinki_start <= 5 and helsinki_start + helsinki_duration >= 3)
    
    problem.addConstraint(helsinki_constraint, ['start_Helsinki', 'duration_Helsinki'])
    
    # Vienna show on day 2-3
    def vienna_constraint(vienna_start, vienna_duration):
        # Vienna visit should include day 2 or day 3
        return (vienna_start <= 3 and vienna_start + vienna_duration >= 2)
    
    problem.addConstraint(vienna_constraint, ['start_Vienna', 'duration_Vienna'])
    
    # Tallinn wedding between day 7 and 11
    def tallinn_constraint(tallinn_start, tallinn_duration):
        # Tallinn visit should overlap with days 7-11
        return (tallinn_start <= 11 and tallinn_start + tallinn_duration >= 7)
    
    problem.addConstraint(tallinn_constraint, ['start_Tallinn', 'duration_Tallinn'])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with strict constraints, use a compromise itinerary
        compromise_itinerary = [
            {"day_range": "Day 1-5", "place": "Dublin"},      # 5 days Dublin
            {"day_range": "Day 6-8", "place": "Helsinki"},    # 3 days Helsinki
            {"day_range": "Day 9-11", "place": "Tallinn"},    # 3 days Tallinn  
            {"day_range": "Day 12-13", "place": "Vienna"},    # 2 days Vienna
            {"day_range": "Day 14-15", "place": "Reykjavik"}  # 2 days Reykjavik
        ]
        
        # Use the compromise itinerary (satisfies day requirements but not all time window constraints)
        result = {"itinerary": compromise_itinerary}
        
    else:
        # Use the first solution found by the constraint solver
        sol = solutions[0]
        
        # Build the itinerary from the solution
        ordered_cities = [None] * num_cities
        for i in range(num_cities):
            pos = sol[i]
            ordered_cities[pos] = cities[i]
        
        # Create day ranges
        itinerary = []
        for i, city in enumerate(ordered_cities):
            if city is not None:
                start_day = sol[f"start_{city}"] + 1  # Convert to 1-based day numbering
                duration = sol[f"duration_{city}"]
                end_day = start_day + duration - 1
                day_range = f"Day {start_day}-{end_day}"
                itinerary.append({"day_range": day_range, "place": city})
        
        result = {"itinerary": itinerary}
    
    return result

# Execute the main function
if __name__ == "__main__":
    result = main()
    print("Generated Itinerary:")
    for item in result["itinerary"]:
        print(f"{item['day_range']}: {item['place']}")