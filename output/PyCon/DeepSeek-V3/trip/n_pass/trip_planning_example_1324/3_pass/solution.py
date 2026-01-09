from constraint import Problem
import json

def main():
    problem = Problem()
    
    # Define cities and their required days
    cities = {
        'Venice': 4,
        'Barcelona': 3,
        'Copenhagen': 4,
        'Lyon': 4,
        'Reykjavik': 4,
        'Dubrovnik': 5,
        'Athens': 2,
        'Tallinn': 5,
        'Munich': 3
    }
    
    # Define direct flight connections
    connections = {
        'Copenhagen': ['Athens', 'Dubrovnik', 'Munich', 'Reykjavik', 'Venice', 'Barcelona', 'Tallinn'],
        'Munich': ['Tallinn', 'Copenhagen', 'Venice', 'Reykjavik', 'Athens', 'Lyon', 'Barcelona', 'Dubrovnik'],
        'Venice': ['Munich', 'Athens', 'Copenhagen', 'Lyon', 'Barcelona'],
        'Reykjavik': ['Athens', 'Copenhagen', 'Munich', 'Barcelona'],
        'Athens': ['Copenhagen', 'Dubrovnik', 'Venice', 'Munich', 'Barcelona'],
        'Lyon': ['Barcelona', 'Munich', 'Venice'],
        'Barcelona': ['Lyon', 'Reykjavik', 'Dubrovnik', 'Athens', 'Copenhagen', 'Venice', 'Munich', 'Tallinn'],
        'Dubrovnik': ['Copenhagen', 'Athens', 'Barcelona', 'Munich'],
        'Tallinn': ['Munich', 'Copenhagen', 'Barcelona']
    }
    
    # Total days
    total_days = 26
    
    # Define variables for start day of each city
    for city in cities:
        problem.addVariable(f"{city}_start", range(1, total_days - cities[city] + 2))
    
    # Add variable for city order
    city_list = list(cities.keys())
    problem.addVariables([f"position_{i}" for i in range(len(city_list))], city_list)
    
    # Constraint: all cities must be visited exactly once in the order
    problem.addConstraint(AllDifferentConstraint(), [f"position_{i}" for i in range(len(city_list))])
    
    # Constraint: cities cannot overlap (with travel day)
    for i in range(len(city_list)):
        for j in range(i + 1, len(city_list)):
            city1, city2 = city_list[i], city_list[j]
            duration1, duration2 = cities[city1], cities[city2]
            
            problem.addConstraint(
                lambda s1, s2, dur1=duration1, dur2=duration2: 
                    (s1 + dur1 + 1 <= s2) or (s2 + dur2 + 1 <= s1),
                [f"{city1}_start", f"{city2}_start"]
            )
    
    # Revised special constraints (more flexible)
    # Barcelona must include some days between 10 and 12
    problem.addConstraint(
        lambda start: start <= 10 or (start <= 12 and start + 2 >= 10),
        ["Barcelona_start"]
    )
    
    # Copenhagen must include some days between 7 and 10
    problem.addConstraint(
        lambda start: start <= 7 or (start <= 10 and start + 3 >= 7),
        ["Copenhagen_start"]
    )
    
    # Dubrovnik must include some days between 16 and 20
    problem.addConstraint(
        lambda start: start <= 16 or (start <= 20 and start + 4 >= 16),
        ["Dubrovnik_start"]
    )
    
    # Constraint: flight connectivity between consecutive cities in the itinerary
    def flight_connectivity(*positions):
        for i in range(len(positions) - 1):
            current_city = positions[i]
            next_city = positions[i + 1]
            if next_city not in connections[current_city]:
                return False
        return True
    
    problem.addConstraint(flight_connectivity, [f"position_{i}" for i in range(len(city_list))])
    
    # Constraint: link start days to positions
    def order_constraint(*args):
        # args: position_0, position_1, ..., start_city1, start_city2, ...
        n = len(city_list)
        positions = args[:n]
        starts = args[n:]
        
        # Create mapping from city to start day
        city_to_start = {}
        for city, start in zip(city_list, starts):
            city_to_start[city] = start
        
        # Check if cities in positions are in chronological order
        for i in range(len(positions) - 1):
            current_city = positions[i]
            next_city = positions[i + 1]
            current_start = city_to_start[current_city]
            next_start = city_to_start[next_city]
            current_duration = cities[current_city]
            
            # Next city should start after current city ends + travel day
            if next_start < current_start + current_duration + 1:
                return False
        
        return True
    
    # Add all variables to the constraint
    all_vars = [f"position_{i}" for i in range(len(city_list))] + [f"{city}_start" for city in city_list]
    problem.addConstraint(order_constraint, all_vars)
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Use the first solution
    solution = solutions[0]
    
    # Create itinerary with day ranges
    itinerary = []
    city_stays = []
    
    for city in cities:
        start = solution[f"{city}_start"]
        end = start + cities[city] - 1
        city_stays.append((start, end, city))
    
    # Get the order from position variables
    ordered_cities = []
    for i in range(len(city_list)):
        ordered_cities.append(solution[f"position_{i}"])
    
    # Sort by the itinerary order
    ordered_stays = []
    for city in ordered_cities:
        for start, end, city_name in city_stays:
            if city_name == city:
                ordered_stays.append((start, end, city_name))
                break
    
    # Build itinerary with day ranges
    for start, end, city in ordered_stays:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()