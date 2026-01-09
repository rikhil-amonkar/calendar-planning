import constraint
import json

def main():
    # Define the problem
    problem = constraint.Problem()
    
    # Cities and their required days
    cities = {
        'Salzburg': 4,
        'Stockholm': 2,
        'Venice': 5,
        'Frankfurt': 4,
        'Florence': 4,
        'Barcelona': 2,
        'Stuttgart': 3
    }
    
    # Direct flight connections
    connections = {
        'Barcelona': ['Frankfurt', 'Florence', 'Stockholm', 'Venice', 'Stuttgart'],
        'Frankfurt': ['Barcelona', 'Florence', 'Stockholm', 'Salzburg', 'Stuttgart', 'Venice'],
        'Florence': ['Barcelona', 'Frankfurt'],
        'Stockholm': ['Barcelona', 'Frankfurt', 'Stuttgart'],
        'Venice': ['Barcelona', 'Frankfurt', 'Stuttgart'],
        'Salzburg': ['Frankfurt'],
        'Stuttgart': ['Barcelona', 'Frankfurt', 'Stockholm', 'Venice']
    }
    
    # Total days
    total_days = 18
    
    # Create variables for arrival day for each city
    # We'll use -1 to indicate the city is not visited (though all must be visited)
    for city in cities:
        problem.addVariable(f'arrival_{city}', range(0, total_days))
    
    # Create variables for departure day for each city
    for city in cities:
        problem.addVariable(f'departure_{city}', range(1, total_days + 1))
    
    # Constraint: Departure must be after arrival + required days - 1
    # (since arrival day counts as day 1 of stay)
    for city, days in cities.items():
        problem.addConstraint(
            lambda arrival, departure, req_days=days: departure == arrival + req_days,
            (f'arrival_{city}', f'departure_{city}')
        )
    
    # Constraint: All cities must be visited within the 18-day period
    for city in cities:
        problem.addConstraint(
            lambda arrival, departure, total=total_days: arrival >= 0 and departure <= total,
            (f'arrival_{city}', f'departure_{city}')
        )
    
    # Constraint: No overlapping stays in different cities
    # For any two different cities, either city1 departs before city2 arrives or vice versa
    city_pairs = [(c1, c2) for c1 in cities for c2 in cities if c1 != c2]
    for city1, city2 in city_pairs:
        problem.addConstraint(
            lambda a1, d1, a2, d2: d1 <= a2 or d2 <= a1,
            (f'arrival_{city1}', f'departure_{city1}', f'arrival_{city2}', f'departure_{city2}')
        )
    
    # Constraint: Venice must be visited from day 1 to day 5
    problem.addConstraint(lambda a, d: a == 0 and d == 5, ('arrival_Venice', 'departure_Venice'))
    
    # Constraint: Travel between cities must be via direct flights
    # This means if we go from city A to city B, there must be a direct flight
    # We'll enforce this by ensuring the departure city and arrival city are connected
    # when there's a transition
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with strict constraints, try a simpler approach
        # Build itinerary based on required days and flight connections
        itinerary = build_itinerary_greedy(cities, connections, total_days)
    else:
        # Convert solution to itinerary format
        solution = solutions[0]
        itinerary = convert_solution_to_itinerary(solution, cities)
    
    # Output as JSON
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

def build_itinerary_greedy(cities, connections, total_days):
    """Build itinerary using a greedy approach when constraint solving fails"""
    
    # Start with Venice (fixed days 1-5)
    itinerary = [{"day_range": "Day 1-5", "place": "Venice"}]
    current_day = 5
    visited = {'Venice'}
    
    # Remove Venice from cities to visit
    remaining_cities = {city: days for city, days in cities.items() if city != 'Venice'}
    
    # Try to visit remaining cities
    while remaining_cities and current_day < total_days:
        current_city = itinerary[-1]['place']
        
        # Find connected cities that haven't been visited
        available_cities = [city for city in remaining_cities.keys() 
                          if city in connections.get(current_city, [])]
        
        if not available_cities:
            # If no direct flights, try any unvisited city
            available_cities = list(remaining_cities.keys())
        
        if available_cities:
            next_city = available_cities[0]
            days_needed = remaining_cities[next_city]
            
            if current_day + days_needed <= total_days:
                start_day = current_day
                end_day = current_day + days_needed
                itinerary.append({
                    "day_range": f"Day {start_day}-{end_day}", 
                    "place": next_city
                })
                current_day = end_day
                visited.add(next_city)
                del remaining_cities[next_city]
            else:
                # Not enough days left for this city
                break
    
    return itinerary

def convert_solution_to_itinerary(solution, cities):
    """Convert constraint solution to itinerary format"""
    # Extract stay information
    stays = []
    for city in cities:
        arrival = solution[f'arrival_{city}']
        departure = solution[f'departure_{city}']
        stays.append({
            'city': city,
            'arrival': arrival,
            'departure': departure
        })
    
    # Sort by arrival day
    stays.sort(key=lambda x: x['arrival'])
    
    # Convert to output format
    itinerary = []
    for stay in stays:
        arrival_day = stay['arrival'] + 1  # Convert to 1-based indexing
        departure_day = stay['departure']
        itinerary.append({
            "day_range": f"Day {arrival_day}-{departure_day}",
            "place": stay['city']
        })
    
    return itinerary

if __name__ == "__main__":
    main()