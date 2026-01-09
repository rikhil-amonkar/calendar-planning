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
    
    # Define direct flight connections
    direct_flights = {
        'Milan': ['Stockholm', 'Munich', 'Seville'],
        'Stockholm': ['Milan', 'Munich', 'Tallinn'],
        'Munich': ['Stockholm', 'Bucharest', 'Seville', 'Milan', 'Tallinn'],
        'Bucharest': ['Munich'],
        'Seville': ['Munich', 'Milan'],
        'Tallinn': ['Stockholm', 'Munich']
    }
    
    # Create variables for start day of each city
    # We'll use -1 to indicate the city is not visited
    for city in cities:
        problem.addVariable(f"{city}_start", range(-1, 18))
        problem.addVariable(f"{city}_end", range(-1, 19))
    
    # Constraint 1: Total days must be exactly 18
    def total_days_constraint(*args):
        city_starts = args[:6]
        city_ends = args[6:]
        cities_list = list(cities.keys())
        
        # Calculate total days by summing durations
        total = 0
        for i, city in enumerate(cities_list):
            start = city_starts[i]
            end = city_ends[i]
            if start != -1 and end != -1 and start <= end:
                total += (end - start + 1)
        
        return total == 18
    
    problem.addConstraint(total_days_constraint, 
                         [f"{city}_start" for city in cities] + [f"{city}_end" for city in cities])
    
    # Constraint 2: Each city must be visited for exactly its required duration
    for city, duration in cities.items():
        def duration_constraint(start, end, dur=duration):
            if start == -1 and end == -1:
                return True  # City not visited
            if start != -1 and end != -1:
                return end - start + 1 == dur
            return False
        
        problem.addConstraint(duration_constraint, [f"{city}_start", f"{city}_end"])
    
    # Constraint 3: Time windows for specific cities
    # Bucharest between day 1 and day 4 (inclusive)
    def bucharest_time_window(start, end):
        if start == -1:
            return False
        return start >= 1 and end <= 4
    
    problem.addConstraint(bucharest_time_window, ['Bucharest_start', 'Bucharest_end'])
    
    # Seville between day 8 and day 12 (inclusive)
    def seville_time_window(start, end):
        if start == -1:
            return False
        return start >= 8 and end <= 12
    
    problem.addConstraint(seville_time_window, ['Seville_start', 'Seville_end'])
    
    # Munich between day 4 and day 8 (inclusive)
    def munich_time_window(start, end):
        if start == -1:
            return False
        return start >= 4 and end <= 8
    
    problem.addConstraint(munich_time_window, ['Munich_start', 'Munich_end'])
    
    # Constraint 4: No overlapping stays (cities visited sequentially)
    def no_overlap_constraint(*args):
        city_starts = args[:6]
        city_ends = args[6:]
        cities_list = list(cities.keys())
        
        # Check all pairs of cities for overlap
        for i in range(len(cities_list)):
            for j in range(i + 1, len(cities_list)):
                start_i, end_i = city_starts[i], city_ends[i]
                start_j, end_j = city_starts[j], city_ends[j]
                
                # Skip if either city is not visited
                if start_i == -1 or start_j == -1:
                    continue
                
                # Check for overlap
                if not (end_i < start_j or end_j < start_i):
                    return False
        
        return True
    
    problem.addConstraint(no_overlap_constraint, 
                         [f"{city}_start" for city in cities] + [f"{city}_end" for city in cities])
    
    # Constraint 5: Flight connectivity
    def flight_connectivity_constraint(*args):
        city_starts = args[:6]
        city_ends = args[6:]
        cities_list = list(cities.keys())
        
        # Create a sequence of city visits
        visits = []
        for i, city in enumerate(cities_list):
            if city_starts[i] != -1:
                visits.append((city_starts[i], city_ends[i], city))
        
        # Sort by start day
        visits.sort()
        
        # Check connectivity between consecutive visits
        for i in range(len(visits) - 1):
            current_city = visits[i][2]
            next_city = visits[i + 1][2]
            
            # Check if there's a direct flight
            if next_city not in direct_flights[current_city]:
                return False
        
        return True
    
    problem.addConstraint(flight_connectivity_constraint, 
                         [f"{city}_start" for city in cities] + [f"{city}_end" for city in cities])
    
    # Constraint 6: All cities must be visited
    def all_cities_visited(*args):
        city_starts = args[:6]
        return all(start != -1 for start in city_starts)
    
    problem.addConstraint(all_cities_visited, [f"{city}_start" for city in cities])
    
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
    
    # Create visit entries
    visits = []
    for city in cities_list:
        start = solution[f"{city}_start"]
        end = solution[f"{city}_end"]
        visits.append((start, end, city))
    
    # Sort by start day
    visits.sort()
    
    # Create the final itinerary
    for start, end, city in visits:
        if start == end:
            day_range = f"Day {start + 1}"
        else:
            day_range = f"Day {start + 1}-{end + 1}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()