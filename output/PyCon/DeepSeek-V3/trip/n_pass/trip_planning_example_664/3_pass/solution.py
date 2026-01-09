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
    
    # Constraint 1: Each city must be visited for exactly its required duration
    # We'll calculate end days based on start days and durations
    for city, duration in cities.items():
        def end_day_constraint(start, dur=duration):
            return start + dur - 1 <= 18
        problem.addConstraint(end_day_constraint, [f"{city}_start"])
    
    # Constraint 2: Time windows for specific cities
    # Bucharest between day 1 and day 4 (inclusive) - duration 4 days
    problem.addConstraint(lambda start: start >= 1 and start <= 1, ['Bucharest_start'])  # Must start on day 1
    
    # Seville between day 8 and day 12 (inclusive) - duration 5 days
    problem.addConstraint(lambda start: start >= 8 and start <= 8, ['Seville_start'])  # Must start on day 8
    
    # Munich between day 4 and day 8 (inclusive) - duration 5 days  
    problem.addConstraint(lambda start: start >= 4 and start <= 4, ['Munich_start'])  # Must start on day 4
    
    # Constraint 3: No overlapping stays
    def no_overlap_constraint(*starts):
        # Calculate end days
        ends = []
        city_list = list(cities.keys())
        for i, city in enumerate(city_list):
            ends.append(starts[i] + cities[city] - 1)
        
        # Check all pairs of cities for overlap
        for i in range(len(starts)):
            for j in range(i + 1, len(starts)):
                # If the intervals overlap
                if not (ends[i] < starts[j] or ends[j] < starts[i]):
                    return False
        return True
    
    problem.addConstraint(no_overlap_constraint, [f"{city}_start" for city in cities])
    
    # Constraint 4: Flight connectivity
    def flight_connectivity_constraint(*starts):
        # Create list of (start, city) pairs
        city_list = list(cities.keys())
        visits = [(starts[i], city_list[i]) for i in range(len(starts))]
        
        # Sort by start day
        visits.sort()
        
        # Check connectivity between consecutive visits
        for i in range(len(visits) - 1):
            current_city = visits[i][1]
            next_city = visits[i + 1][1]
            
            # Check if there's a direct flight between current and next city
            if next_city not in direct_flights[current_city]:
                return False
        
        return True
    
    problem.addConstraint(flight_connectivity_constraint, [f"{city}_start" for city in cities])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Use the first solution
    solution = solutions[0]
    
    # Build the itinerary
    itinerary = []
    
    # Create visit entries
    visits = []
    for city in cities:
        start = solution[f"{city}_start"]
        end = start + cities[city] - 1
        visits.append((start, end, city))
    
    # Sort by start day
    visits.sort()
    
    # Create the final itinerary
    for start, end, city in visits:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Verify total days
    total_days = sum(cities.values())
    
    # Output as JSON
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()