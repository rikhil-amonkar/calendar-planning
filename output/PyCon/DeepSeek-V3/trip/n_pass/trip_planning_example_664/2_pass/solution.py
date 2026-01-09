import constraint
import json

def main():
    problem = constraint.Problem()
    
    # Define the cities and their required stay durations
    cities = {
        'Tallinn': 2,
        'Bucharest': 4,
        'Seville': 5,
        'Stockholm': 5,
        'Munich': 5,
        'Milan': 2
    }
    
    # Define direct flight connections (bidirectional)
    direct_flights = {
        'Milan': ['Stockholm', 'Munich', 'Seville'],
        'Stockholm': ['Milan', 'Munich', 'Tallinn'],
        'Munich': ['Stockholm', 'Bucharest', 'Seville', 'Milan', 'Tallinn'],
        'Bucharest': ['Munich'],
        'Seville': ['Munich', 'Milan'],
        'Tallinn': ['Stockholm', 'Munich']
    }
    
    # Create variables for start day of each city (1-based indexing)
    for city in cities:
        problem.addVariable(f"{city}_start", range(1, 19))  # Days 1-18
        problem.addVariable(f"{city}_end", range(1, 19))    # Days 1-18
    
    # Constraint 1: Each city must be visited for exactly its required duration
    for city, duration in cities.items():
        def duration_constraint(start, end, dur=duration):
            return end - start + 1 == dur
        
        problem.addConstraint(duration_constraint, [f"{city}_start", f"{city}_end"])
    
    # Constraint 2: Time windows for specific cities
    # Bucharest between day 1 and day 4 (inclusive)
    def bucharest_time_window(start, end):
        return start >= 1 and end <= 4
    
    problem.addConstraint(bucharest_time_window, ['Bucharest_start', 'Bucharest_end'])
    
    # Seville between day 8 and day 12 (inclusive)
    def seville_time_window(start, end):
        return start >= 8 and end <= 12
    
    problem.addConstraint(seville_time_window, ['Seville_start', 'Seville_end'])
    
    # Munich between day 4 and day 8 (inclusive)
    def munich_time_window(start, end):
        return start >= 4 and end <= 8
    
    problem.addConstraint(munich_time_window, ['Munich_start', 'Munich_end'])
    
    # Constraint 3: No overlapping stays
    def no_overlap_constraint(*args):
        city_starts = args[::2]  # Every other element is a start day
        city_ends = args[1::2]   # Every other element is an end day
        
        # Check all pairs of cities for overlap
        for i in range(len(city_starts)):
            for j in range(i + 1, len(city_starts)):
                start_i, end_i = city_starts[i], city_ends[i]
                start_j, end_j = city_starts[j], city_ends[j]
                
                # Check for overlap
                if not (end_i < start_j or end_j < start_i):
                    return False
        
        return True
    
    # Add all start and end variables to the constraint
    all_vars = []
    for city in cities:
        all_vars.extend([f"{city}_start", f"{city}_end"])
    
    problem.addConstraint(no_overlap_constraint, all_vars)
    
    # Constraint 4: Total days must be exactly 18
    def total_days_constraint(*args):
        total = 0
        for i in range(0, len(args), 2):
            start, end = args[i], args[i+1]
            total += (end - start + 1)
        return total == 18
    
    problem.addConstraint(total_days_constraint, all_vars)
    
    # Constraint 5: Flight connectivity - we need to ensure consecutive cities in the sequence are connected
    # Since we don't know the visit order in advance, we'll use a different approach
    # We'll create an ordering variable and ensure consecutive cities in the order are connected
    
    # Add variables to represent the visit order
    for i, city in enumerate(cities):
        problem.addVariable(f"order_{city}", range(len(cities)))
    
    # Constraint: All order values must be unique
    problem.addConstraint(constraint.AllDifferentConstraint(), [f"order_{city}" for city in cities])
    
    # Flight connectivity constraint
    def flight_connectivity_constraint(*args):
        # Extract order values and start days
        order_values = args[:len(cities)]
        start_days = args[len(cities):2*len(cities)]
        
        # Create a list of (order, start_day, city) tuples
        city_order = list(cities.keys())
        visits = []
        for i, city in enumerate(city_order):
            visits.append((order_values[i], start_days[i], city))
        
        # Sort by order
        visits.sort()
        
        # Check connectivity between consecutive visits
        for i in range(len(visits) - 1):
            current_city = visits[i][2]
            next_city = visits[i + 1][2]
            
            # Check if there's a direct flight
            if next_city not in direct_flights[current_city]:
                return False
        
        return True
    
    # Add the flight connectivity constraint
    connectivity_vars = [f"order_{city}" for city in cities] + [f"{city}_start" for city in cities]
    problem.addConstraint(flight_connectivity_constraint, connectivity_vars)
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Use the first solution
    solution = solutions[0]
    
    # Build the itinerary
    itinerary = []
    cities_list = list(cities.keys())
    
    # Create visit entries using order information
    visits = []
    for city in cities_list:
        start = solution[f"{city}_start"]
        end = solution[f"{city}_end"]
        order = solution[f"order_{city}"]
        visits.append((order, start, end, city))
    
    # Sort by order
    visits.sort()
    
    # Create the final itinerary
    for order, start, end, city in visits:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()