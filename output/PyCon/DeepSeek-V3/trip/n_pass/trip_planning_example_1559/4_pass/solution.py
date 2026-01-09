import json
from constraint import Problem, AllDifferentConstraint
import itertools

def main():
    # Define cities and their required days
    cities = {
        'Valencia': 2,
        'Oslo': 3,
        'Lyon': 4,
        'Prague': 3,
        'Paris': 4,
        'Nice': 4,
        'Seville': 5,
        'Tallinn': 2,
        'Mykonos': 5,
        'Lisbon': 2
    }
    
    # Define direct flight connections
    connections = {
        'Lisbon': ['Paris', 'Seville', 'Prague', 'Valencia', 'Nice', 'Oslo', 'Lyon'],
        'Paris': ['Lisbon', 'Oslo', 'Valencia', 'Nice', 'Lyon', 'Tallinn', 'Prague', 'Seville'],
        'Lyon': ['Nice', 'Prague', 'Paris', 'Valencia', 'Oslo'],
        'Nice': ['Lyon', 'Paris', 'Mykonos', 'Oslo', 'Lisbon'],
        'Oslo': ['Tallinn', 'Paris', 'Prague', 'Nice', 'Lyon', 'Lisbon'],
        'Seville': ['Lisbon', 'Paris', 'Valencia'],
        'Tallinn': ['Oslo', 'Paris', 'Prague'],
        'Mykonos': ['Nice'],
        'Prague': ['Lyon', 'Lisbon', 'Oslo', 'Paris', 'Valencia', 'Tallinn'],
        'Valencia': ['Paris', 'Lisbon', 'Lyon', 'Seville', 'Prague']
    }
    
    # Define special constraints
    special_constraints = [
        ('Valencia', 3, 4),  # Valencia between day 3-4
        ('Oslo', 13, 15),    # Oslo between day 13-15
        ('Seville', 5, 9),   # Seville between day 5-9
        ('Mykonos', 21, 25)  # Mykonos between day 21-25
    ]
    
    problem = Problem()
    
    # Create variables for start day of each city visit
    city_vars = {}
    for city in cities:
        city_vars[city] = f"start_{city}"
    
    # Add variables with domain (possible start days)
    total_days = 25
    for city, var_name in city_vars.items():
        max_start = total_days - cities[city] + 1
        
        # Apply special constraints to limit domain
        special_constraint_applied = False
        for special_city, min_day, max_day in special_constraints:
            if city == special_city:
                # Constrain start day to ensure the visit overlaps with the required window
                min_start = max(1, min_day - cities[city] + 1)
                max_start = min(max_start, max_day)
                problem.addVariable(var_name, range(min_start, max_start + 1))
                special_constraint_applied = True
                break
        
        if not special_constraint_applied:
            problem.addVariable(var_name, range(1, max_start + 1))
    
    # Constraint: No overlapping visits
    for i, city1 in enumerate(cities):
        for j, city2 in enumerate(cities):
            if i < j:
                var1 = city_vars[city1]
                var2 = city_vars[city2]
                dur1 = cities[city1]
                dur2 = cities[city2]
                
                problem.addConstraint(
                    lambda s1, s2, d1=dur1, d2=dur2: (s1 + d1 <= s2) or (s2 + d2 <= s1),
                    (var1, var2)
                )
    
    # Additional constraint: Ensure special time windows are respected
    for city, min_day, max_day in special_constraints:
        var_name = city_vars[city]
        dur = cities[city]
        
        problem.addConstraint(
            lambda start, d=dur, min_d=min_day, max_d=max_day: 
            start <= max_d and start + d - 1 >= min_d,
            (var_name,)
        )
    
    # Solve the problem to get possible day assignments
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid day assignment found"}))
        return
    
    print(f"Found {len(solutions)} valid day assignments. Now checking for connected itineraries...")
    
    # For each valid day assignment, check if we can create a valid travel sequence
    for solution_idx, solution in enumerate(solutions):
        # Create a list of city visits with start and end days
        visits = []
        for city in cities:
            start_day = solution[city_vars[city]]
            end_day = start_day + cities[city] - 1
            visits.append((city, start_day, end_day))
        
        # Sort by start day to get chronological order
        visits.sort(key=lambda x: x[1])
        
        # Generate all possible permutations and check for valid connections
        city_names = [city for city, _, _ in visits]
        
        # Try different starting cities
        for start_city in city_names:
            remaining_cities = city_names.copy()
            remaining_cities.remove(start_city)
            
            # Generate permutations of remaining cities
            for perm in itertools.permutations(remaining_cities):
                sequence = [start_city] + list(perm)
                
                # Check if this sequence is valid
                valid = True
                for i in range(len(sequence) - 1):
                    current_city = sequence[i]
                    next_city = sequence[i + 1]
                    
                    # Get visit information
                    current_visit = next(v for v in visits if v[0] == current_city)
                    next_visit = next(v for v in visits if v[0] == next_city)
                    
                    current_end = current_visit[2]
                    next_start = next_visit[1]
                    
                    # Check connection and timing
                    if (next_city not in connections.get(current_city, []) or 
                        next_start <= current_end):  # Should be > current_end, but we have travel day
                        valid = False
                        break
                
                if valid:
                    # Create itinerary
                    itinerary = []
                    for city_name in sequence:
                        visit = next(v for v in visits if v[0] == city_name)
                        start_day, end_day = visit[1], visit[2]
                        day_range = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
                        itinerary.append({
                            "day_range": day_range,
                            "place": city_name
                        })
                    
                    # Add travel days information
                    travel_info = []
                    for i in range(len(sequence) - 1):
                        current_city = sequence[i]
                        next_city = sequence[i + 1]
                        current_end = next(v[2] for v in visits if v[0] == current_city)
                        next_start = next(v[1] for v in visits if v[0] == next_city)
                        travel_day = current_end + 1
                        travel_info.append(f"Travel from {current_city} to {next_city} on Day {travel_day}")
                    
                    print(json.dumps({
                        "itinerary": itinerary,
                        "travel_days": travel_info
                    }, indent=2))
                    return
        
        if solution_idx % 100 == 0 and solution_idx > 0:
            print(f"Checked {solution_idx} solutions...")
    
    # If no valid sequence found, try a simpler approach with fixed start city
    print("Trying alternative approach with Lisbon as starting point...")
    
    # Use Lisbon as starting city (good connectivity)
    for solution in solutions:
        visits = []
        for city in cities:
            start_day = solution[city_vars[city]]
            end_day = start_day + cities[city] - 1
            visits.append((city, start_day, end_day))
        
        visits.sort(key=lambda x: x[1])
        
        # Build sequence starting from Lisbon
        sequence = ['Lisbon']
        remaining = [city for city in cities if city != 'Lisbon']
        
        def build_sequence(current_city, remaining_cities, current_sequence):
            if not remaining_cities:
                return current_sequence
            
            current_visit = next(v for v in visits if v[0] == current_city)
            current_end = current_visit[2]
            
            # Try cities that are connected and start after current visit ends
            possible_next = []
            for next_city in remaining_cities:
                if next_city in connections.get(current_city, []):
                    next_visit = next(v for v in visits if v[0] == next_city)
                    if next_visit[1] > current_end:  # Next city starts after current ends
                        possible_next.append(next_city)
            
            # Sort by start day for better chance of finding valid sequence
            possible_next.sort(key=lambda city: next(v[1] for v in visits if v[0] == city))
            
            for next_city in possible_next:
                new_remaining = remaining_cities.copy()
                new_remaining.remove(next_city)
                result = build_sequence(next_city, new_remaining, current_sequence + [next_city])
                if result:
                    return result
            
            return None
        
        final_sequence = build_sequence('Lisbon', remaining, ['Lisbon'])
        if final_sequence:
            itinerary = []
            for city_name in final_sequence:
                visit = next(v for v in visits if v[0] == city_name)
                start_day, end_day = visit[1], visit[2]
                day_range = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
                itinerary.append({
                    "day_range": day_range,
                    "place": city_name
                })
            
            print(json.dumps({"itinerary": itinerary}, indent=2))
            return
    
    print(json.dumps({"error": "No valid itinerary with connected flights found"}))

if __name__ == "__main__":
    main()