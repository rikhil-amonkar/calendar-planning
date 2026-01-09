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
    city_list = list(cities.keys())
    
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
    
    # SIMPLIFIED APPROACH: Add variables for visit order
    position_vars = {}
    for city in city_list:
        position_vars[city] = f"pos_{city}"
        problem.addVariable(f"pos_{city}", range(len(city_list)))
    
    # Constraint: All positions must be unique
    problem.addConstraint(AllDifferentConstraint(), [f"pos_{city}" for city in city_list])
    
    # Constraint: Visit order must match chronological order of start days
    def start_days_match_positions(*args):
        # Extract start days and positions from args
        start_days = args[:len(city_list)]
        positions = args[len(city_list):]
        
        # Create mapping of cities to start days and positions
        city_start_map = {}
        city_pos_map = {}
        for i, city in enumerate(city_list):
            city_start_map[city] = start_days[i]
            city_pos_map[city] = positions[i]
        
        # For each pair of cities, if one has lower position, it should have earlier start day
        for city1 in city_list:
            for city2 in city_list:
                if city1 != city2:
                    pos1 = city_pos_map[city1]
                    pos2 = city_pos_map[city2]
                    start1 = city_start_map[city1]
                    start2 = city_start_map[city2]
                    
                    # If city1 comes before city2 in position, city1 should end before city2 starts
                    if pos1 < pos2:
                        end1 = start1 + cities[city1] - 1
                        if end1 >= start2:
                            return False
        
        return True
    
    # Combine all variables for the constraint
    all_vars = list(city_vars.values()) + [f"pos_{city}" for city in city_list]
    problem.addConstraint(start_days_match_positions, all_vars)
    
    # Constraint: Flight connectivity between consecutive cities in visit order
    def check_flight_connectivity(*positions):
        # Map positions to cities
        pos_to_city = {}
        for city in city_list:
            pos_to_city[positions[city_list.index(city)]] = city
        
        # Check connectivity between consecutive positions
        for pos in range(len(city_list) - 1):
            current_city = pos_to_city.get(pos)
            next_city = pos_to_city.get(pos + 1)
            
            if current_city and next_city:
                if next_city not in flight_connections.get(current_city, []):
                    return False
        return True
    
    problem.addConstraint(check_flight_connectivity, [f"pos_{city}" for city in city_list])
    
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
    
    # Extract visit order
    visit_order = []
    for city in city_list:
        visit_order.append((solution[f"pos_{city}"], city))
    visit_order.sort()
    visit_order = [city for _, city in visit_order]
    
    # Create itinerary with day ranges
    itinerary = []
    for city in visit_order:
        start_day = city_starts[city]
        end_day = start_day + cities[city] - 1
        day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Verify all constraints are satisfied
    total_used_days = sum(cities.values())
    if total_used_days > total_days:
        print(json.dumps({"error": f"Total days exceeded: {total_used_days} > {total_days}"}))
        return
    
    # Verify flight connectivity
    for i in range(len(visit_order) - 1):
        current = visit_order[i]
        next_city = visit_order[i + 1]
        if next_city not in flight_connections.get(current, []):
            print(json.dumps({"error": f"No flight from {current} to {next_city}"}))
            return
    
    # Verify special constraints
    prague_start = city_starts['Prague']
    prague_end = prague_start + cities['Prague'] - 1
    if not (7 <= prague_start <= 9 or 7 <= prague_end <= 9):
        print(json.dumps({"error": "Prague not visited between days 7-9"}))
        return
    
    mykonos_start = city_starts['Mykonos']
    mykonos_end = mykonos_start + cities['Mykonos'] - 1
    if not (1 <= mykonos_start <= 3 or 1 <= mykonos_end <= 3):
        print(json.dumps({"error": "Mykonos not visited between days 1-3"}))
        return
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()