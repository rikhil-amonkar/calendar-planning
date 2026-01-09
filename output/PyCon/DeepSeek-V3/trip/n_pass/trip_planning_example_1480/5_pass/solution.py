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
    
    # Special constraints - fixed start dates
    special_constraints = {
        'Geneva': {'start': 1, 'end': 5},      # Must start in Geneva on days 1-5
        'Venice': {'start': 6, 'end': 12},     # Must start in Venice on days 6-12  
        'Vilnius': {'start': 19, 'end': 24},   # Must start in Vilnius on days 19-24
        'Brussels': {'start': 25, 'end': 26}   # Must start in Brussels on days 25-26
    }
    
    # Create variables: position in itinerary -> city
    num_cities = len(cities)
    positions = list(range(num_cities))
    
    # Add variables for which city is at each position
    problem.addVariables(positions, list(cities.keys()))
    problem.addConstraint(AllDifferentConstraint(), positions)
    
    # Add variables for start day of each position
    for pos in positions:
        problem.addVariable(f"start_{pos}", range(1, total_days + 1))
    
    # Constraint 1: Special start date constraints
    for pos in positions:
        def special_start_constraint(city, start_day, pos=pos, special_constraints=special_constraints):
            if city in special_constraints:
                constraint = special_constraints[city]
                return constraint['start'] <= start_day <= constraint['end']
            return True
        problem.addConstraint(special_start_constraint, [pos, f"start_{pos}"])
    
    # Constraint 2: Flight connectivity between consecutive cities
    for pos in range(num_cities - 1):
        def flight_connectivity(city1, city2, flights=flights):
            return city2 in flights[city1]
        problem.addConstraint(flight_connectivity, [pos, pos + 1])
    
    # Constraint 3: Visit duration and travel day sequencing
    for pos in range(num_cities - 1):
        def visit_sequence(start_current, start_next, city_current, cities=cities):
            duration_current = cities[city_current]
            # Next city must start at least 1 day after current city ends (travel day)
            return start_current + duration_current <= start_next
        problem.addConstraint(visit_sequence, [f"start_{pos}", f"start_{pos + 1}", pos])
    
    # Constraint 4: All visits must fit within total days
    for pos in positions:
        def within_total_days(start_day, city, cities=cities, total_days=total_days):
            duration = cities[city]
            return start_day + duration - 1 <= total_days
        problem.addConstraint(within_total_days, [f"start_{pos}", pos])
    
    # Constraint 5: Ensure special constraint cities are visited in reasonable order
    # This helps the solver by providing guidance
    def special_order_constraint(*cities_in_order):
        special_cities_order = []
        for city in cities_in_order:
            if city in special_constraints:
                special_cities_order.append(city)
        
        # Check if special cities appear in chronological order of their constraints
        for i in range(len(special_cities_order) - 1):
            city1 = special_cities_order[i]
            city2 = special_cities_order[i + 1]
            if special_constraints[city1]['start'] > special_constraints[city2]['start']:
                return False
        return True
    
    problem.addConstraint(special_order_constraint, positions)
    
    # Try to find a solution
    solution = problem.getSolution()
    
    if not solution:
        # Try a more relaxed approach for special constraints
        print("Trying relaxed constraints...")
        
        # Relax the special constraints to allow ending after the window
        for pos in positions:
            problem.getConstraint(lambda city, start_day, pos=pos: True if city not in special_constraints else True)
        
        # Add relaxed special constraints (only start day matters)
        for pos in positions:
            def relaxed_special_constraint(city, start_day, special_constraints=special_constraints):
                if city in special_constraints:
                    constraint = special_constraints[city]
                    return start_day >= constraint['start'] and start_day <= constraint['end']
                return True
            problem.addConstraint(relaxed_special_constraint, [pos, f"start_{pos}"])
        
        solution = problem.getSolution()
    
    if not solution:
        print('{"itinerary": [], "error": "No valid itinerary found with given constraints"}')
        return
    
    # Build and output the itinerary
    itinerary = []
    for pos in range(num_cities):
        city = solution[pos]
        start_day = solution[f"start_{pos}"]
        duration = cities[city]
        end_day = start_day + duration - 1
        
        if start_day == end_day:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{end_day}"
        
        itinerary.append({
            'day_range': day_range,
            'place': city
        })
    
    # Sort by start day
    itinerary.sort(key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
    
    result = {'itinerary': itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()