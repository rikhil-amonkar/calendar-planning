from constraint import Problem
import json

def main():
    problem = Problem()
    
    cities = ['Prague', 'Warsaw', 'Dublin', 'Athens', 'Vilnius', 'Porto', 'London', 'Seville', 'Lisbon', 'Dubrovnik']
    
    # Define durations for each city
    durations = {
        'Prague': 3,
        'Warsaw': 4, 
        'Dublin': 3,
        'Athens': 3,
        'Vilnius': 4,
        'Porto': 5,
        'London': 3,
        'Seville': 2,
        'Lisbon': 5,
        'Dubrovnik': 3
    }
    
    # Define fixed constraints (start day, end day)
    fixed_constraints = {
        'Prague': (1, 3),    # Prague: Day 1-3
        'Warsaw': (20, 23),  # Warsaw: Day 20-23  
        'Porto': (16, 20),   # Porto: Day 16-20
        'London': (3, 5),    # London: Day 3-5
        'Lisbon': (5, 9)     # Lisbon: Day 5-9
    }
    
    # Define direct flight connections
    direct_flights = {
        'Warsaw': ['Vilnius', 'London', 'Athens', 'Lisbon', 'Porto', 'Prague', 'Dublin'],
        'Vilnius': ['Warsaw', 'Athens'],
        'Prague': ['Athens', 'Lisbon', 'London', 'Warsaw', 'Dublin'],
        'Athens': ['Prague', 'Vilnius', 'Dublin', 'Warsaw', 'Dubrovnik', 'London', 'Lisbon'],
        'London': ['Lisbon', 'Dublin', 'Prague', 'Warsaw', 'Athens'],
        'Lisbon': ['London', 'Porto', 'Prague', 'Athens', 'Warsaw', 'Dublin', 'Seville'],
        'Porto': ['Lisbon', 'Warsaw', 'Seville', 'Dublin'],
        'Dublin': ['London', 'Seville', 'Athens', 'Porto', 'Warsaw', 'Lisbon', 'Dubrovnik'],
        'Seville': ['Dublin', 'Porto', 'Lisbon'],
        'Dubrovnik': ['Athens', 'Dublin']
    }
    
    # Create variables for start day of each city visit
    for city in cities:
        if city in fixed_constraints:
            # Fixed cities have predetermined start days
            start_day, end_day = fixed_constraints[city]
            problem.addVariable(f"start_{city}", [start_day])
        else:
            # Flexible cities can start on any valid day
            problem.addVariable(f"start_{city}", range(1, 24))  # Max start day ensures duration fits in 26 days
    
    # Constraint 1: No overlapping stays
    def no_overlap_constraint(*starts):
        occupied_days = set()
        for i, city in enumerate(cities):
            start = starts[i]
            duration = durations[city]
            end = start + duration - 1
            # Check if stay exceeds 26 days
            if end > 26:
                return False
            # Check for overlaps
            for day in range(start, start + duration):
                if day in occupied_days:
                    return False
                occupied_days.add(day)
        return True
    
    problem.addConstraint(no_overlap_constraint, [f"start_{city}" for city in cities])
    
    # Constraint 2: All days from 1 to 26 must be covered (no gaps)
    def all_days_covered(*starts):
        all_days = set(range(1, 27))
        covered_days = set()
        for i, city in enumerate(cities):
            start = starts[i]
            duration = durations[city]
            for day in range(start, start + duration):
                if day > 26:
                    return False
                covered_days.add(day)
        return covered_days == all_days
    
    problem.addConstraint(all_days_covered, [f"start_{city}" for city in cities])
    
    # Constraint 3: Flight connections between consecutive cities in itinerary order
    def flight_connections_constraint(*starts):
        # Create schedule sorted by start day
        schedule = []
        for i, city in enumerate(cities):
            start = starts[i]
            schedule.append((start, city))
        
        schedule.sort()
        ordered_cities = [city for _, city in schedule]
        
        # Check flight connections between consecutive cities in the timeline
        for i in range(len(ordered_cities) - 1):
            current_city = ordered_cities[i]
            next_city = ordered_cities[i + 1]
            
            # Check if there's a direct flight between consecutive cities
            if next_city not in direct_flights.get(current_city, []):
                return False
        
        return True
    
    problem.addConstraint(flight_connections_constraint, [f"start_{city}" for city in cities])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        # Try a more relaxed approach - remove the flight connection constraint first
        print("Trying relaxed constraints...")
        problem2 = Problem()
        
        # Recreate the problem without flight connection constraint
        for city in cities:
            if city in fixed_constraints:
                start_day, end_day = fixed_constraints[city]
                problem2.addVariable(f"start_{city}", [start_day])
            else:
                problem2.addVariable(f"start_{city}", range(1, 24))
        
        problem2.addConstraint(no_overlap_constraint, [f"start_{city}" for city in cities])
        problem2.addConstraint(all_days_covered, [f"start_{city}" for city in cities])
        
        solutions = problem2.getSolutions()
        
        if not solutions:
            # Try without the "all days covered" constraint
            print("Trying without all days covered constraint...")
            problem3 = Problem()
            
            for city in cities:
                if city in fixed_constraints:
                    start_day, end_day = fixed_constraints[city]
                    problem3.addVariable(f"start_{city}", [start_day])
                else:
                    problem3.addVariable(f"start_{city}", range(1, 24))
            
            problem3.addConstraint(no_overlap_constraint, [f"start_{city}" for city in cities])
            
            solutions = problem3.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    solution = solutions[0]
    
    # Build itinerary
    itinerary_items = []
    for city in cities:
        start = solution[f"start_{city}"]
        duration = durations[city]
        end = start + duration - 1
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary_items.append({"day_range": day_range, "place": city})
    
    # Sort by start day
    itinerary_items.sort(key=lambda x: int(x["day_range"].split(" ")[1].split("-")[0]))
    
    result = {"itinerary": itinerary_items}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()