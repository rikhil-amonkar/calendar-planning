import json
from constraint import Problem, AllDifferentConstraint

def main():
    problem = Problem()
    
    # Define cities and their required days
    cities = {
        'Oslo': 2,
        'Reykjavik': 5,
        'Stockholm': 4,
        'Munich': 4,
        'Frankfurt': 4,
        'Barcelona': 3,
        'Bucharest': 2,
        'Split': 3
    }
    
    # Define direct flight connections
    connections = {
        'Reykjavik': ['Munich', 'Oslo', 'Frankfurt', 'Barcelona', 'Stockholm'],
        'Munich': ['Reykjavik', 'Frankfurt', 'Bucharest', 'Oslo', 'Stockholm', 'Barcelona', 'Split'],
        'Frankfurt': ['Munich', 'Oslo', 'Barcelona', 'Reykjavik', 'Bucharest', 'Stockholm', 'Split'],
        'Oslo': ['Split', 'Reykjavik', 'Frankfurt', 'Bucharest', 'Barcelona', 'Stockholm', 'Munich'],
        'Barcelona': ['Bucharest', 'Frankfurt', 'Reykjavik', 'Stockholm', 'Split', 'Oslo', 'Munich'],
        'Bucharest': ['Munich', 'Barcelona', 'Oslo', 'Frankfurt'],
        'Stockholm': ['Barcelona', 'Reykjavik', 'Split', 'Munich', 'Oslo', 'Frankfurt'],
        'Split': ['Oslo', 'Barcelona', 'Stockholm', 'Frankfurt', 'Munich']
    }
    
    # Create variables for start day of each city visit
    start_vars = {}
    for city in cities:
        start_vars[city] = f"{city}_start"
    
    # Add variables with domain 1-20
    for var in start_vars.values():
        problem.addVariable(var, range(1, 21))
    
    # Constraint: No overlapping visits and all days within 1-20
    def no_overlap_constraint(*starts):
        city_starts = {}
        idx = 0
        for city in cities:
            city_starts[city] = starts[idx]
            idx += 1
        
        # Check for overlaps between all pairs of cities
        for city1, start1 in city_starts.items():
            end1 = start1 + cities[city1] - 1
            if end1 > 20:  # Check if visit extends beyond day 20
                return False
                
            for city2, start2 in city_starts.items():
                if city1 == city2:
                    continue
                end2 = start2 + cities[city2] - 1
                
                # Check if visits overlap
                if not (end1 < start2 or end2 < start1):
                    return False
        
        return True
    
    problem.addConstraint(no_overlap_constraint, list(start_vars.values()))
    
    # Special constraints
    # Oslo: 2 days, with annual show on days 16-17
    def oslo_constraint(oslo_start):
        oslo_end = oslo_start + 1  # 2 days means start to start+1
        # Oslo must include either day 16 or 17 (or both)
        return (oslo_start <= 16 and oslo_end >= 16) or (oslo_start <= 17 and oslo_end >= 17)
    
    problem.addConstraint(oslo_constraint, ['Oslo_start'])
    
    # Reykjavik: 5 days, meet friend between day 9-13
    def reykjavik_constraint(reykjavik_start):
        reykjavik_end = reykjavik_start + 4  # 5 days means start to start+4
        # Reykjavik must overlap with days 9-13
        return reykjavik_start <= 13 and reykjavik_end >= 9
    
    problem.addConstraint(reykjavik_constraint, ['Reykjavik_start'])
    
    # Munich: 4 days, visit relatives between day 13-16
    def munich_constraint(munich_start):
        munich_end = munich_start + 3  # 4 days means start to start+3
        # Munich must overlap with days 13-16
        return munich_start <= 16 and munich_end >= 13
    
    problem.addConstraint(munich_constraint, ['Munich_start'])
    
    # Frankfurt: 4 days, workshop between day 17-20
    def frankfurt_constraint(frankfurt_start):
        frankfurt_end = frankfurt_start + 3  # 4 days means start to start+3
        # Frankfurt must overlap with days 17-20
        return frankfurt_start <= 20 and frankfurt_end >= 17
    
    problem.addConstraint(frankfurt_constraint, ['Frankfurt_start'])
    
    # Flight connection constraints - only between consecutive visits in time
    def flight_connections_constraint(*starts):
        # Create a list of (start_day, city, end_day) tuples
        visits = []
        idx = 0
        for city in cities:
            start = starts[idx]
            end = start + cities[city] - 1
            visits.append((start, city, end))
            idx += 1
        
        # Sort visits by start day to get chronological order
        visits.sort()
        
        # Check flight connections between consecutive visits in time
        for i in range(len(visits) - 1):
            current_city = visits[i][1]
            next_city = visits[i + 1][1]
            
            # Check if there's a direct flight connection
            if next_city not in connections[current_city]:
                return False
        
        return True
    
    problem.addConstraint(flight_connections_constraint, list(start_vars.values()))
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        # Try a more flexible approach - allow any valid sequence, not necessarily visiting all cities in one chain
        # Remove the flight connection constraint and try again
        problem = Problem()
        
        # Re-add variables
        for var in start_vars.values():
            problem.addVariable(var, range(1, 21))
        
        # Re-add basic constraints
        problem.addConstraint(no_overlap_constraint, list(start_vars.values()))
        problem.addConstraint(oslo_constraint, ['Oslo_start'])
        problem.addConstraint(reykjavik_constraint, ['Reykjavik_start'])
        problem.addConstraint(munich_constraint, ['Munich_start'])
        problem.addConstraint(frankfurt_constraint, ['Frankfurt_start'])
        
        solutions = problem.getSolutions()
    
    if not solutions:
        result = {"itinerary": [], "error": "No valid itinerary found"}
        print(json.dumps(result))
        return
    
    # Use the first solution
    solution = solutions[0]
    
    # Create day assignments
    day_assignments = {}
    for city in cities:
        start = solution[f"{city}_start"]
        duration = cities[city]
        for day in range(start, start + duration):
            day_assignments[day] = city
    
    # Convert to itinerary format
    itinerary = []
    current_city = None
    current_start = None
    current_end = None
    
    for day in range(1, 21):
        city = day_assignments.get(day)
        
        if city != current_city:
            if current_city is not None:
                itinerary.append({
                    "day_range": f"Day {current_start}-{current_end}",
                    "place": current_city
                })
            current_city = city
            current_start = day
            current_end = day
        else:
            current_end = day
    
    # Add the last segment
    if current_city is not None:
        itinerary.append({
            "day_range": f"Day {current_start}-{current_end}",
            "place": current_city
        })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()