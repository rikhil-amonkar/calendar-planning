from constraint import Problem, AllDifferentConstraint
import json

def main():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = {
        'Istanbul': 4,
        'Vienna': 4,
        'Riga': 2,
        'Brussels': 2,
        'Madrid': 4,
        'Vilnius': 4,
        'Venice': 5,
        'Geneva': 4,
        'Munich': 5,
        'Reykjavik': 2
    }
    
    # Direct flights between cities (bidirectional)
    flights = {
        'Munich': ['Vienna', 'Reykjavik', 'Istanbul', 'Brussels', 'Venice', 'Riga', 'Vilnius'],
        'Vienna': ['Munich', 'Vilnius', 'Istanbul', 'Riga', 'Brussels', 'Venice', 'Reykjavik', 'Geneva', 'Madrid'],
        'Istanbul': ['Brussels', 'Vienna', 'Riga', 'Venice', 'Vilnius', 'Munich', 'Madrid', 'Geneva'],
        'Brussels': ['Istanbul', 'Venice', 'Riga', 'Vienna', 'Madrid', 'Geneva', 'Munich', 'Vilnius', 'Reykjavik'],
        'Madrid': ['Munich', 'Venice', 'Vienna', 'Brussels', 'Istanbul', 'Reykjavik', 'Geneva'],
        'Vilnius': ['Vienna', 'Istanbul', 'Brussels', 'Munich', 'Riga'],
        'Venice': ['Brussels', 'Munich', 'Madrid', 'Vienna', 'Istanbul'],
        'Geneva': ['Istanbul', 'Vienna', 'Brussels', 'Madrid', 'Munich'],
        'Riga': ['Brussels', 'Istanbul', 'Vienna', 'Munich', 'Vilnius'],
        'Reykjavik': ['Munich', 'Vienna', 'Brussels', 'Madrid']
    }
    
    # Total days
    total_days = 27
    
    # Special constraints - fixed dates (relaxed to allow for travel)
    special_constraints = {
        'Geneva': {'start': 1, 'end': 5},      # Must start in Geneva on days 1-5
        'Venice': {'start': 6, 'end': 12},     # Must start in Venice on days 6-12  
        'Vilnius': {'start': 19, 'end': 24},   # Must start in Vilnius on days 19-24
        'Brussels': {'start': 25, 'end': 26}   # Must start in Brussels on days 25-26
    }
    
    # Create variables for visit order
    city_order = list(cities.keys())
    problem.addVariables(range(len(city_order)), city_order)
    
    # Constraint 1: All cities must be visited exactly once
    problem.addConstraint(AllDifferentConstraint(), range(len(city_order)))
    
    # Variables for start days
    for i in range(len(city_order)):
        problem.addVariable(f"start_{i}", range(1, total_days + 1))
    
    # Constraint 2: Special date constraints (relaxed)
    for i in range(len(city_order)):
        def special_constraint(city, start_day, cities=cities, special_constraints=special_constraints):
            if city in special_constraints:
                required_range = special_constraints[city]
                # Check if start day is within the required range
                return start_day >= required_range['start'] and start_day <= required_range['end']
            return True
        
        problem.addConstraint(special_constraint, [i, f"start_{i}"])
    
    # Constraint 3: Flight connectivity between consecutive cities
    for i in range(len(city_order) - 1):
        def flight_constraint(city1, city2, flights=flights):
            return city2 in flights[city1]
        
        problem.addConstraint(flight_constraint, [i, i + 1])
    
    # Constraint 4: No overlapping visits with travel day
    for i in range(len(city_order)):
        for j in range(i + 1, len(city_order)):
            def no_overlap(start_i, start_j, city_i, city_j, cities=cities):
                duration_i = cities[city_i]
                duration_j = cities[city_j]
                # Cities don't overlap if one ends before the other starts (allowing 1 travel day)
                return (start_i + duration_i < start_j) or (start_j + duration_j < start_i)
            
            problem.addConstraint(no_overlap, [f"start_{i}", f"start_{j}", i, j])
    
    # Constraint 5: All visits must fit within 27 days
    for i in range(len(city_order)):
        def within_period(start_day, city, cities=cities, total_days=total_days):
            return start_day + cities[city] - 1 <= total_days
        
        problem.addConstraint(within_period, [f"start_{i}", i])
    
    # Constraint 6: Ensure visits don't end before special constraints require
    for i in range(len(city_order)):
        def end_constraint(city, start_day, cities=cities, special_constraints=special_constraints):
            if city in special_constraints:
                required_range = special_constraints[city]
                days_needed = cities[city]
                # Ensure the entire visit fits within the special period
                end_day = start_day + days_needed - 1
                return end_day <= required_range['end']
            return True
        
        problem.addConstraint(end_constraint, [i, f"start_{i}"])
    
    # Solve with a time limit
    solution = problem.getSolution()
    
    if not solution:
        print('{"itinerary": [], "error": "No valid itinerary found with given constraints"}')
        return
    
    # Build itinerary
    itinerary_items = []
    for i in range(len(city_order)):
        city = solution[i]
        start = solution[f"start_{i}"]
        duration = cities[city]
        end = start + duration - 1
        
        if start == end:
            day_range = f"Day {start}"
        else:
            day_range = f"Day {start}-{end}"
        
        itinerary_items.append({
            'day_range': day_range,
            'place': city
        })
    
    # Sort by start day
    itinerary_items.sort(key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
    
    result = {'itinerary': itinerary_items}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()