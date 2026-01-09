import json
from constraint import Problem, AllDifferentConstraint

def solve_trip_plan():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = {
        'Helsinki': 4,
        'Valencia': 5,
        'Dubrovnik': 4,
        'Porto': 3,
        'Prague': 3,
        'Reykjavik': 4
    }
    
    # Direct flight connections
    connections = {
        'Helsinki': ['Prague', 'Reykjavik', 'Dubrovnik'],
        'Prague': ['Helsinki', 'Valencia', 'Reykjavik'],
        'Valencia': ['Prague', 'Porto'],
        'Porto': ['Valencia'],
        'Dubrovnik': ['Helsinki'],
        'Reykjavik': ['Helsinki', 'Prague']
    }
    
    # Create variables for visit order (position in itinerary)
    city_vars = list(cities.keys())
    problem.addVariables(city_vars, range(len(cities)))
    problem.addConstraint(AllDifferentConstraint(), city_vars)
    
    # Constraint: Porto must be visited between day 16-18 (last 3 days)
    # This means Porto should be in one of the last 3 positions
    def porto_last_constraint(porto_pos, *positions):
        return porto_pos >= len(cities) - 3
    
    problem.addConstraint(porto_last_constraint, ['Porto'] + city_vars)
    
    # Constraint: Cities must be connected by direct flights
    def flight_connections_constraint(*positions):
        order = sorted(zip(positions, city_vars))
        for i in range(len(order) - 1):
            city1 = order[i][1]
            city2 = order[i + 1][1]
            if city2 not in connections[city1]:
                return False
        return True
    
    problem.addConstraint(flight_connections_constraint, city_vars)
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Convert solution to ordered list of cities
    ordered_cities = sorted([(pos, city) for city, pos in solution.items()])
    itinerary_order = [city for pos, city in ordered_cities]
    
    # Calculate day ranges
    itinerary = []
    current_day = 1
    
    for i, city in enumerate(itinerary_order):
        duration = cities[city]
        end_day = current_day + duration - 1
        
        # Check if this is the last city
        if i == len(itinerary_order) - 1:
            day_range = f"Day {current_day}-{end_day}"
        else:
            day_range = f"Day {current_day}-{end_day}"
        
        itinerary.append({
            "day_range": day_range,
            "place": city
        })
        
        current_day = end_day + 1
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_trip_plan()
    print(json.dumps(result, indent=2))