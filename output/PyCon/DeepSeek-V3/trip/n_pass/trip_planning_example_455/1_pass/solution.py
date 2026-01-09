import json
from constraint import Problem

def solve_trip_plan():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = ['Reykjavik', 'Riga', 'Warsaw', 'Istanbul', 'Krakow']
    required_days = {
        'Reykjavik': 7,
        'Riga': 2,
        'Warsaw': 3,
        'Istanbul': 6,
        'Krakow': 7
    }
    
    total_days = 21
    
    # Direct flight connections
    direct_flights = [
        ('Istanbul', 'Krakow'),
        ('Warsaw', 'Reykjavik'),
        ('Istanbul', 'Warsaw'),
        ('Riga', 'Istanbul'),
        ('Krakow', 'Warsaw'),
        ('Riga', 'Warsaw')
    ]
    
    # Make the graph undirected
    flight_graph = {}
    for city1, city2 in direct_flights:
        if city1 not in flight_graph:
            flight_graph[city1] = set()
        if city2 not in flight_graph:
            flight_graph[city2] = set()
        flight_graph[city1].add(city2)
        flight_graph[city2].add(city1)
    
    # Define the order variables (which city is visited in which position)
    num_cities = len(cities)
    positions = list(range(num_cities))
    
    # Add variables for city order
    problem.addVariables(positions, cities)
    
    # Constraint: All cities must be visited exactly once in the itinerary
    problem.addConstraint(lambda *cities_visited: len(set(cities_visited)) == num_cities, positions)
    
    # Constraint: Consecutive cities must have direct flights
    def flight_constraint(city1, city2):
        if city1 == city2:
            return False
        return city2 in flight_graph.get(city1, set())
    
    for i in range(num_cities - 1):
        problem.addConstraint(flight_constraint, [i, i + 1])
    
    # Find all possible valid orders
    valid_orders = problem.getSolutions()
    
    # For each valid order, check if we can assign days that satisfy all constraints
    valid_itineraries = []
    
    for order_solution in valid_orders:
        # Extract the city order from the solution
        city_order = [order_solution[i] for i in range(num_cities)]
        
        # Try to assign days to each city visit
        # We'll use a backtracking approach to assign days
        
        def assign_days_to_cities(current_index, day_allocations, remaining_days_per_city):
            if current_index == num_cities:
                # Check if all days are allocated correctly
                if all(days == 0 for days in remaining_days_per_city.values()):
                    return day_allocations
                return None
            
            current_city = city_order[current_index]
            required = remaining_days_per_city[current_city]
            
            if required == 0:
                return assign_days_to_cities(current_index + 1, day_allocations, remaining_days_per_city.copy())
            
            # Try allocating the required days to this city
            new_allocations = day_allocations.copy()
            new_remaining = remaining_days_per_city.copy()
            
            new_allocations.append((current_city, required))
            new_remaining[current_city] = 0
            
            result = assign_days_to_cities(current_index + 1, new_allocations, new_remaining)
            if result is not None:
                return result
            
            return None
        
        # Initialize remaining days
        remaining_days = required_days.copy()
        
        # Try to assign days
        day_allocations = assign_days_to_cities(0, [], remaining_days)
        
        if day_allocations is not None:
            # Check if total days match
            total_allocated = sum(days for city, days in day_allocations)
            if total_allocated == total_days:
                valid_itineraries.append((city_order, day_allocations))
    
    # If we found valid itineraries, pick the first one and format it
    if valid_itineraries:
        city_order, day_allocations = valid_itineraries[0]
        
        # Build the itinerary with day ranges
        itinerary = []
        current_day = 1
        
        for city, days in day_allocations:
            if days > 0:
                end_day = current_day + days - 1
                if current_day == end_day:
                    day_range = f"Day {current_day}"
                else:
                    day_range = f"Day {current_day}-{end_day}"
                itinerary.append({"day_range": day_range, "place": city})
                current_day = end_day + 1
        
        return {"itinerary": itinerary}
    
    return {"itinerary": []}

if __name__ == "__main__":
    result = solve_trip_plan()
    print(json.dumps(result, indent=2))