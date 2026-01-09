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
    
    # Constraint: All start days must be different
    problem.addConstraint(AllDifferentConstraint(), list(start_vars.values()))
    
    # Constraint: Each city must have required number of consecutive days
    def consecutive_days_constraint(*starts):
        all_days = set()
        city_starts = {}
        idx = 0
        for city in cities:
            city_starts[city] = starts[idx]
            idx += 1
        
        # Check for overlaps and validate consecutive days
        for city, start in city_starts.items():
            duration = cities[city]
            city_days = set(range(start, start + duration))
            
            # Check if any days exceed 20
            if max(city_days) > 20:
                return False
            
            # Check for overlaps with other cities
            for other_city, other_start in city_starts.items():
                if city == other_city:
                    continue
                other_duration = cities[other_city]
                other_days = set(range(other_start, other_start + other_duration))
                if city_days.intersection(other_days):
                    return False
            
            all_days.update(city_days)
        
        # Check if all 20 days are covered
        if len(all_days) != 20:
            return False
        
        return True
    
    problem.addConstraint(consecutive_days_constraint, list(start_vars.values()))
    
    # Special constraints
    # Oslo: 2 days, with annual show on days 16-17
    def oslo_constraint(oslo_start):
        return (oslo_start <= 16 and oslo_start + 2 > 16) or (oslo_start == 15)
    
    problem.addConstraint(oslo_constraint, ['Oslo_start'])
    
    # Reykjavik: 5 days, meet friend between day 9-13
    def reykjavik_constraint(reykjavik_start):
        reykjavik_end = reykjavik_start + 5 - 1
        return reykjavik_start <= 13 and reykjavik_end >= 9
    
    problem.addConstraint(reykjavik_constraint, ['Reykjavik_start'])
    
    # Munich: 4 days, visit relatives between day 13-16
    def munich_constraint(munich_start):
        munich_end = munich_start + 4 - 1
        return munich_start <= 16 and munich_end >= 13
    
    problem.addConstraint(munich_constraint, ['Munich_start'])
    
    # Frankfurt: 4 days, workshop between day 17-20
    def frankfurt_constraint(frankfurt_start):
        frankfurt_end = frankfurt_start + 4 - 1
        return frankfurt_start <= 20 and frankfurt_end >= 17
    
    problem.addConstraint(frankfurt_constraint, ['Frankfurt_start'])
    
    # Flight connection constraints
    def flight_connections_constraint(*starts):
        city_order = []
        for city in cities:
            city_order.append(city)
        
        # Create day-city mapping
        day_city = {}
        idx = 0
        for city in city_order:
            start = starts[idx]
            duration = cities[city]
            for day in range(start, start + duration):
                day_city[day] = city
            idx += 1
        
        # Check flight connections between consecutive city visits
        days = sorted(day_city.keys())
        for i in range(len(days) - 1):
            current_city = day_city[days[i]]
            next_city = day_city[days[i + 1]]
            
            # If consecutive days are in different cities, check flight connection
            if current_city != next_city:
                if next_city not in connections[current_city]:
                    return False
        
        return True
    
    problem.addConstraint(flight_connections_constraint, list(start_vars.values()))
    
    # Solve the problem
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
        city = day_assignments[day]
        
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