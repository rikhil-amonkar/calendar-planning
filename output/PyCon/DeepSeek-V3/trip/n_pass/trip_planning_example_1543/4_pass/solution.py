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
        # Try alternative approach: allow flexible ordering that respects flight connections
        print("Trying alternative approach with flexible ordering...")
        
        # Create a new problem that explicitly models visit order
        problem_alt = Problem()
        
        # We'll use position variables to represent the visit order
        for i, city in enumerate(cities):
            if city in fixed_constraints:
                start_day, end_day = fixed_constraints[city]
                problem_alt.addVariable(f"start_{city}", [start_day])
            else:
                problem_alt.addVariable(f"start_{city}", range(1, 24))
            
            # Position in the itinerary (1 to 10)
            problem_alt.addVariable(f"pos_{city}", range(1, 11))
        
        # No overlap constraint
        problem_alt.addConstraint(no_overlap_constraint, [f"start_{city}" for city in cities])
        
        # All days covered constraint  
        problem_alt.addConstraint(all_days_covered, [f"start_{city}" for city in cities])
        
        # All positions must be unique
        problem_alt.addConstraint(lambda *positions: len(set(positions)) == len(positions), 
                                [f"pos_{city}" for city in cities])
        
        # Flight connection constraint based on position
        def flight_by_position_constraint(*args):
            # args contains: start days and positions interleaved
            starts = args[:len(cities)]
            positions = args[len(cities):]
            
            # Create mapping from position to city
            pos_to_city = {}
            for i, city in enumerate(cities):
                pos = positions[i]
                pos_to_city[pos] = city
            
            # Check flights between consecutive positions
            for pos in range(1, 10):
                if pos not in pos_to_city or (pos + 1) not in pos_to_city:
                    continue
                current_city = pos_to_city[pos]
                next_city = pos_to_city[pos + 1]
                
                if next_city not in direct_flights.get(current_city, []):
                    return False
            
            return True
        
        problem_alt.addConstraint(flight_by_position_constraint, 
                                [f"start_{city}" for city in cities] + [f"pos_{city}" for city in cities])
        
        alt_solutions = problem_alt.getSolutions()
        valid_solutions = alt_solutions
    
    if not valid_solutions:
        print("Final attempt: relaxing 'all days covered' constraint...")
        problem_final = Problem()
        
        for city in cities:
            if city in fixed_constraints:
                start_day, end_day = fixed_constraints[city]
                problem_final.addVariable(f"start_{city}", [start_day])
            else:
                problem_final.addVariable(f"start_{city}", range(1, 24))
        
        problem_final.addConstraint(no_overlap_constraint, [f"start_{city}" for city in cities])
        
        final_solutions = problem_final.getSolutions()
        
        if final_solutions:
            # Check flight constraints on these solutions
            for solution in final_solutions:
                timeline = []
                for city in cities:
                    start = solution[f"start_{city}"]
                    duration = durations[city]
                    end = start + duration - 1
                    timeline.append((start, end, city))
                
                timeline.sort()
                ordered_cities = [city for _, _, city in timeline]
                
                valid = True
                for i in range(len(ordered_cities) - 1):
                    current_city = ordered_cities[i]
                    next_city = ordered_cities[i + 1]
                    
                    if next_city not in direct_flights.get(current_city, []):
                        valid = False
                        break
                
                if valid:
                    valid_solutions.append(solution)
                    break
    
    if not valid_solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    solution = valid_solutions[0]
    
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