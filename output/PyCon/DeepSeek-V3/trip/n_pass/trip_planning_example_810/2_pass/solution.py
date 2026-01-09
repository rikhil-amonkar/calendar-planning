import json
from constraint import Problem, AllDifferentConstraint

def solve_trip_plan():
    problem = Problem()
    
    # Define cities and their required days
    cities = ['Berlin', 'Nice', 'Athens', 'Stockholm', 'Barcelona', 'Vilnius', 'Lyon']
    required_days = {
        'Berlin': 3,
        'Nice': 5,
        'Athens': 5,
        'Stockholm': 5,
        'Barcelona': 2,
        'Vilnius': 4,
        'Lyon': 2
    }
    
    # Define direct flight connections
    direct_flights = {
        'Lyon': ['Nice'],
        'Stockholm': ['Athens'],
        'Nice': ['Athens', 'Lyon', 'Barcelona', 'Stockholm'],
        'Berlin': ['Athens', 'Nice', 'Barcelona', 'Vilnius', 'Stockholm'],
        'Barcelona': ['Nice', 'Athens', 'Stockholm', 'Lyon', 'Berlin'],
        'Athens': ['Stockholm', 'Nice', 'Berlin', 'Vilnius', 'Barcelona'],
        'Vilnius': ['Berlin', 'Athens']
    }
    
    # Create variables for visit order (position in itinerary)
    positions = list(range(len(cities)))
    problem.addVariables(cities, positions)
    problem.addConstraint(AllDifferentConstraint(), cities)
    
    # Berlin must be first (position 0)
    problem.addConstraint(lambda berlin_pos: berlin_pos == 0, ['Berlin'])
    
    # Barcelona must be second (position 1)
    problem.addConstraint(lambda barcelona_pos: barcelona_pos == 1, ['Barcelona'])
    
    # Lyon must be third (position 2)
    problem.addConstraint(lambda lyon_pos: lyon_pos == 2, ['Lyon'])
    
    # Flight connectivity constraints
    def flight_connectivity(*city_positions):
        # Create a mapping of position to city
        pos_to_city = {pos: city for city, pos in zip(cities, city_positions)}
        
        # Get cities in order
        ordered_cities = [pos_to_city[i] for i in range(len(cities))]
        
        # Check connectivity between consecutive cities
        for i in range(len(ordered_cities) - 1):
            current_city = ordered_cities[i]
            next_city = ordered_cities[i + 1]
            
            # Check if there's a direct flight from current to next city
            if next_city not in direct_flights.get(current_city, []):
                return False
        
        return True
    
    problem.addConstraint(flight_connectivity, cities)
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create ordered list of cities by position
    ordered_cities = sorted([(pos, city) for city, pos in solution.items()])
    
    # Verify total days
    total_calculated_days = sum(required_days[city] for _, city in ordered_cities)
    
    # Build itinerary with day ranges
    itinerary = []
    current_day = 1
    
    for pos, city in ordered_cities:
        days_needed = required_days[city]
        end_day = current_day + days_needed - 1
        
        if days_needed == 1:
            day_range = f"Day {current_day}"
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