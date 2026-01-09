import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and their required days
    cities = {
        'Valencia': 5,
        'Riga': 5,
        'Prague': 3,
        'Mykonos': 3,
        'Zurich': 5,
        'Bucharest': 5,
        'Nice': 2
    }
    
    total_days = 22
    
    # Define direct flight connections (bidirectional)
    flight_connections = {
        'Mykonos': ['Nice', 'Zurich'],
        'Nice': ['Mykonos', 'Riga', 'Zurich'],
        'Zurich': ['Mykonos', 'Prague', 'Riga', 'Bucharest', 'Valencia', 'Nice'],
        'Prague': ['Zurich', 'Bucharest', 'Riga', 'Valencia'],
        'Bucharest': ['Prague', 'Valencia', 'Zurich', 'Riga'],
        'Riga': ['Zurich', 'Bucharest', 'Prague', 'Nice'],
        'Valencia': ['Zurich', 'Bucharest', 'Prague']
    }
    
    # Define special constraints
    prague_constraint = (7, 9)  # Prague between day 7 and 9
    mykonos_constraint = (1, 3)  # Mykonos between day 1 and 3
    
    problem = Problem()
    
    # Create variables for start day of each city visit
    city_vars = {}
    for city in cities:
        city_vars[city] = f"{city}_start"
    
    # Define possible start days (1 to total_days)
    for city, var_name in city_vars.items():
        max_start = total_days - cities[city] + 1
        problem.addVariable(var_name, range(1, max_start + 1))
    
    # Constraint: All cities must be visited exactly once
    problem.addConstraint(AllDifferentConstraint(), list(city_vars.values()))
    
    # Constraint: No overlapping visits
    for city1, days1 in cities.items():
        for city2, days2 in cities.items():
            if city1 != city2:
                start1 = city_vars[city1]
                start2 = city_vars[city2]
                problem.addConstraint(
                    lambda s1, s2, d1=days1, d2=days2: 
                    s1 + d1 <= s2 or s2 + d2 <= s1,
                    [start1, start2]
                )
    
    # Constraint: Special date constraints
    prague_start = city_vars['Prague']
    problem.addConstraint(
        lambda start: prague_constraint[0] <= start <= prague_constraint[1] - cities['Prague'] + 1, 
        [prague_start]
    )
    
    mykonos_start = city_vars['Mykonos']
    problem.addConstraint(
        lambda start: mykonos_constraint[0] <= start <= mykonos_constraint[1] - cities['Mykonos'] + 1, 
        [mykonos_start]
    )
    
    # Constraint: Flight connectivity - consecutive cities must have direct flights
    def check_flight_connectivity(*starts):
        # Create mapping of start days to cities
        start_to_city = {}
        solution = {}
        for city, var_name in city_vars.items():
            idx = list(city_vars.values()).index(var_name)
            start_to_city[starts[idx]] = city
            solution[city] = starts[idx]
        
        # Sort cities by start day
        ordered_starts = sorted(starts)
        ordered_cities = [start_to_city[start] for start in ordered_starts]
        
        # Check consecutive pairs have direct flights
        for i in range(len(ordered_cities) - 1):
            city1 = ordered_cities[i]
            city2 = ordered_cities[i + 1]
            
            if city2 not in flight_connections.get(city1, []):
                return False
        
        return True
    
    # Add flight connectivity constraint
    problem.addConstraint(check_flight_connectivity, list(city_vars.values()))
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Extract start days for each city
    city_starts = {}
    for city, var_name in city_vars.items():
        city_starts[city] = solution[var_name]
    
    # Create itinerary with day ranges
    itinerary = []
    for start_day, city in sorted([(start, city) for city, start in city_starts.items()]):
        end_day = start_day + cities[city] - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()