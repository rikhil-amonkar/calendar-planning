import json
from constraint import Problem, AllDifferentConstraint

def main():
    problem = Problem()
    
    cities = ['Reykjavik', 'Stuttgart', 'Porto', 'Oslo', 'Split', 'Geneva', 'Tallinn', 'Stockholm']
    
    # Define variables for start days of each city visit
    # We'll use start days and durations to calculate the schedule
    start_vars = [f"start_{city}" for city in cities]
    
    # Add variables for start days (1-21)
    for var in start_vars:
        problem.addVariable(var, range(1, 22))
    
    # Add variables for durations (predefined)
    durations = {
        'Reykjavik': 2,
        'Stuttgart': 5, 
        'Porto': 3,
        'Oslo': 5,
        'Split': 3,
        'Geneva': 2,
        'Tallinn': 5,
        'Stockholm': 3
    }
    
    # Add duration variables
    for city in cities:
        problem.addVariable(f"dur_{city}", [durations[city]])
    
    # Constraint: All city visits must be non-overlapping and sequential
    def no_overlap_constraint(*starts):
        start_dict = {}
        for i, city in enumerate(cities):
            start_dict[city] = starts[i]
        
        # Check for overlaps
        for i, city1 in enumerate(cities):
            for j, city2 in enumerate(cities):
                if i != j:
                    start1 = start_dict[city1]
                    start2 = start_dict[city2]
                    dur1 = durations[city1]
                    dur2 = durations[city2]
                    
                    # If visits overlap, constraint is violated
                    if not (start1 + dur1 <= start2 or start2 + dur2 <= start1):
                        return False
        return True
    
    problem.addConstraint(no_overlap_constraint, start_vars)
    
    # Fixed constraints from the problem statement
    # Reykjavik: days 1-2 (conference)
    problem.addConstraint(lambda x: x == 1, ["start_Reykjavik"])
    
    # Porto: days 19-21 (workshop) - start on day 19 for 3 days
    problem.addConstraint(lambda x: x == 19, ["start_Porto"])
    
    # Stockholm: must include days 2-4 (meet friend)
    # This means Stockholm visit must start on day 2, 3, or 4 and last 3 days
    def stockholm_constraint(start):
        return start <= 2 and start + 3 >= 4  # Must cover days 2-4
    
    problem.addConstraint(stockholm_constraint, ["start_Stockholm"])
    
    # Flight connectivity constraints
    flight_routes = {
        'Reykjavik': ['Stuttgart', 'Stockholm', 'Tallinn', 'Oslo'],
        'Stockholm': ['Reykjavik', 'Oslo', 'Stuttgart', 'Split', 'Geneva'],
        'Stuttgart': ['Reykjavik', 'Porto', 'Stockholm', 'Split'],
        'Oslo': ['Stockholm', 'Split', 'Geneva', 'Porto', 'Tallinn'],
        'Split': ['Oslo', 'Stockholm', 'Stuttgart', 'Geneva'],
        'Geneva': ['Oslo', 'Porto', 'Split', 'Stockholm'],
        'Porto': ['Stuttgart', 'Geneva', 'Oslo'],
        'Tallinn': ['Reykjavik', 'Oslo']
    }
    
    def valid_flight_sequence(*starts):
        start_dict = {}
        for i, city in enumerate(cities):
            start_dict[city] = starts[i]
        
        # Create ordered list of city visits by start day
        visits = sorted([(start_dict[city], durations[city], city) for city in cities])
        
        # Check flight connectivity between consecutive visits
        for i in range(len(visits) - 1):
            current_city = visits[i][2]
            next_city = visits[i + 1][2]
            
            # Check if there's a direct flight
            if next_city not in flight_routes[current_city]:
                return False
        
        return True
    
    problem.addConstraint(valid_flight_sequence, start_vars)
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Use the first solution
    solution = solutions[0]
    
    # Build itinerary
    itinerary = []
    visits = []
    
    for city in cities:
        start = solution[f"start_{city}"]
        duration = durations[city]
        visits.append((start, duration, city))
    
    # Sort by start day
    visits.sort()
    
    # Create day ranges
    for start, duration, city in visits:
        end_day = start + duration - 1
        if duration == 1:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Verify total days = 21
    total_days = sum(durations.values())
    if total_days != 21:
        print(json.dumps({"error": f"Total days mismatch: {total_days}"}))
        return
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()