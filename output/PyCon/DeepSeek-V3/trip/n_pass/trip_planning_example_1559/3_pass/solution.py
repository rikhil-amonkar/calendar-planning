import json
from constraint import Problem, AllDifferentConstraint

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
    
    # Special time window constraints
    for city, min_day, max_day in special_constraints:
        var_name = city_vars[city]
        dur = cities[city]
        
        problem.addConstraint(
            lambda start, d=dur, min_d=min_day, max_d=max_day: 
            start <= max_day and start + d - 1 >= min_d,
            (var_name,)
        )
    
    # Solve the problem to get possible day assignments
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid day assignment found"}))
        return
    
    # For each valid day assignment, check if we can create a valid travel sequence
    for solution in solutions:
        # Create a list of city visits with start and end days
        visits = []
        for city in cities:
            start_day = solution[city_vars[city]]
            end_day = start_day + cities[city] - 1
            visits.append((city, start_day, end_day))
        
        # Sort by start day to get chronological order
        visits.sort(key=lambda x: x[1])
        
        # Check if we can find a valid travel sequence with connected flights
        # We need to ensure that for each consecutive pair, there's a flight connection
        # and the travel day (day after previous city ends) is before next city starts
        
        # Try to find a valid sequence using backtracking
        def find_valid_sequence(remaining, current_seq):
            if not remaining:
                return current_seq
            
            last_city = current_seq[-1][0] if current_seq else None
            
            for i, next_visit in enumerate(remaining):
                next_city, next_start, next_end = next_visit
                
                # If this is the first city, just add it
                if last_city is None:
                    new_seq = current_seq + [next_visit]
                    result = find_valid_sequence(remaining[:i] + remaining[i+1:], new_seq)
                    if result:
                        return result
                else:
                    # Check if there's a flight connection and timing works
                    last_end = current_seq[-1][2]
                    travel_day = last_end + 1  # Travel happens the day after last visit ends
                    
                    # Next visit should start after travel day
                    if next_start >= travel_day and next_city in connections.get(last_city, []):
                        new_seq = current_seq + [next_visit]
                        result = find_valid_sequence(remaining[:i] + remaining[i+1:], new_seq)
                        if result:
                            return result
            
            return None
        
        valid_sequence = find_valid_sequence(visits, [])
        
        if valid_sequence:
            # Create itinerary with day ranges
            itinerary = []
            for city, start_day, end_day in valid_sequence:
                day_range = f"Day {start_day}-{end_day}" if start_day != end_day else f"Day {start_day}"
                itinerary.append({
                    "day_range": day_range,
                    "place": city
                })
            
            # Output as JSON
            print(json.dumps({"itinerary": itinerary}, indent=2))
            return
    
    # If no valid sequence found
    print(json.dumps({"error": "No valid itinerary with connected flights found"}))

if __name__ == "__main__":
    main()