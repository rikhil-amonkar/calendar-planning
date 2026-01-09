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
            start_day, end_day = fixed_constraints[city]
            problem.addVariable(f"start_{city}", [start_day])
        else:
            # Flexible cities can start on any valid day
            problem.addVariable(f"start_{city}", range(1, 24))  # Max start day ensures duration fits in 26 days
    
    # Constraint 1: No overlapping stays
    def no_overlap_constraint(*starts):
        intervals = []
        for i, city in enumerate(cities):
            start = starts[i]
            duration = durations[city]
            end = start + duration - 1
            if end > 26:
                return False
            intervals.append((start, end))
        
        # Check all pairs for overlap
        for i in range(len(intervals)):
            for j in range(i + 1, len(intervals)):
                start_i, end_i = intervals[i]
                start_j, end_j = intervals[j]
                if not (end_i < start_j or end_j < start_i):
                    return False
        return True
    
    problem.addConstraint(no_overlap_constraint, [f"start_{city}" for city in cities])
    
    # Constraint 2: All days must be within 1-26 range and visits must be consecutive
    def valid_day_range(*starts):
        all_days = set()
        for i, city in enumerate(cities):
            start = starts[i]
            duration = durations[city]
            end = start + duration - 1
            if end > 26:
                return False
            # Add all days for this city to the set
            for day in range(start, end + 1):
                all_days.add(day)
        
        # Check if all days from min to max are covered (no gaps in the itinerary)
        if len(all_days) > 0:
            min_day = min(all_days)
            max_day = max(all_days)
            expected_days = set(range(min_day, max_day + 1))
            return all_days == expected_days
        
        return False
    
    problem.addConstraint(valid_day_range, [f"start_{city}" for city in cities])
    
    # Solve without flight constraint first to check feasibility
    print("Finding base solution without flight constraints...")
    base_solutions = problem.getSolutions()
    
    if not base_solutions:
        print("No solution found even without flight constraints")
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    print(f"Found {len(base_solutions)} base solutions without flight constraints")
    
    # Now check flight constraints on valid base solutions
    valid_solutions = []
    
    for base_solution in base_solutions:
        # Build the timeline to determine visit order
        timeline = []
        for city in cities:
            start = base_solution[f"start_{city}"]
            duration = durations[city]
            end = start + duration - 1
            timeline.append((start, end, city))
        
        # Sort by start day to get visit order
        timeline.sort()
        ordered_cities = [city for _, _, city in timeline]
        
        # Check flight connections between consecutive cities
        valid = True
        for i in range(len(ordered_cities) - 1):
            current_city = ordered_cities[i]
            next_city = ordered_cities[i + 1]
            
            # Check if there's a direct flight
            if next_city not in direct_flights.get(current_city, []):
                valid = False
                break
        
        if valid:
            valid_solutions.append(base_solution)
    
    if not valid_solutions:
        print("No solution found with flight constraints. Trying alternative approach...")
        
        # Alternative: Use position-based approach with flight constraints
        problem_alt = Problem()
        
        # Add start day variables
        for city in cities:
            if city in fixed_constraints:
                start_day, end_day = fixed_constraints[city]
                problem_alt.addVariable(f"start_{city}", [start_day])
            else:
                problem_alt.addVariable(f"start_{city}", range(1, 24))
        
        # Add position variables for visit order
        positions = list(range(1, 11))
        for city in cities:
            problem_alt.addVariable(f"pos_{city}", positions)
        
        # No overlap constraint
        problem_alt.addConstraint(no_overlap_constraint, [f"start_{city}" for city in cities])
        
        # Valid day range constraint
        problem_alt.addConstraint(valid_day_range, [f"start_{city}" for city in cities])
        
        # All positions must be unique
        problem_alt.addConstraint(lambda *pos: len(set(pos)) == len(pos), 
                                [f"pos_{city}" for city in cities])
        
        # Flight connection constraint: consecutive positions must have direct flights
        def flight_constraint(*args):
            # Extract positions
            positions_dict = {}
            for i, city in enumerate(cities):
                positions_dict[args[i + len(cities)]] = city
            
            # Check flights between consecutive positions
            for pos in range(1, 10):
                if pos in positions_dict and (pos + 1) in positions_dict:
                    from_city = positions_dict[pos]
                    to_city = positions_dict[pos + 1]
                    if to_city not in direct_flights.get(from_city, []):
                        return False
            return True
        
        problem_alt.addConstraint(flight_constraint, 
                                [f"start_{city}" for city in cities] + [f"pos_{city}" for city in cities])
        
        alt_solutions = problem_alt.getSolutions()
        if alt_solutions:
            valid_solutions = alt_solutions
            print(f"Found {len(valid_solutions)} solutions with alternative approach")
    
    if not valid_solutions:
        print("Final attempt: checking if fixed constraints themselves are problematic...")
        
        # Let's verify the fixed constraints don't overlap
        fixed_intervals = []
        for city, (start, end) in fixed_constraints.items():
            fixed_intervals.append((start, end, city))
        
        fixed_intervals.sort()
        for i in range(len(fixed_intervals) - 1):
            current_start, current_end, current_city = fixed_intervals[i]
            next_start, next_end, next_city = fixed_intervals[i + 1]
            if current_end >= next_start:
                print(f"Conflict detected: {current_city} ({current_start}-{current_end}) overlaps with {next_city} ({next_start}-{next_end})")
        
        print(json.dumps({"error": "No valid itinerary found that satisfies all constraints"}))
        return
    
    # Use the first valid solution
    solution = valid_solutions[0]
    
    # Build itinerary
    timeline = []
    for city in cities:
        start = solution[f"start_{city}"]
        duration = durations[city]
        end = start + duration - 1
        timeline.append((start, end, city))
    
    # Sort by start day
    timeline.sort()
    
    itinerary_items = []
    for start, end, city in timeline:
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        itinerary_items.append({"day_range": day_range, "place": city})
    
    result = {"itinerary": itinerary_items}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()