import constraint
import json

def main():
    # Define the problem
    problem = constraint.Problem()
    
    # Cities and their required days
    cities = ['Amsterdam', 'Edinburgh', 'Brussels', 'Vienna', 'Berlin', 'Reykjavik']
    required_days = {
        'Amsterdam': 4,
        'Edinburgh': 5,
        'Brussels': 5,
        'Vienna': 5,
        'Berlin': 4,
        'Reykjavik': 5
    }
    
    # Direct flight connections
    direct_flights = [
        ('Edinburgh', 'Berlin'), ('Amsterdam', 'Berlin'), ('Edinburgh', 'Amsterdam'),
        ('Vienna', 'Berlin'), ('Berlin', 'Brussels'), ('Vienna', 'Reykjavik'),
        ('Edinburgh', 'Brussels'), ('Vienna', 'Brussels'), ('Amsterdam', 'Reykjavik'),
        ('Reykjavik', 'Brussels'), ('Amsterdam', 'Vienna'), ('Reykjavik', 'Berlin')
    ]
    
    # Make flight connections bidirectional
    flight_connections = {}
    for city1, city2 in direct_flights:
        if city1 not in flight_connections:
            flight_connections[city1] = set()
        if city2 not in flight_connections:
            flight_connections[city2] = set()
        flight_connections[city1].add(city2)
        flight_connections[city2].add(city1)
    
    # Create variables for visit order and durations
    # We'll represent the itinerary as a sequence of visits
    max_visits = 6  # Maximum number of city visits (one per city)
    
    # Variables: visit_i_city, visit_i_start_day, visit_i_duration for i in 0..max_visits-1
    visit_vars = []
    
    for i in range(max_visits):
        problem.addVariable(f'visit_{i}_city', cities)
        problem.addVariable(f'visit_{i}_start_day', range(1, 24))
        problem.addVariable(f'visit_{i}_duration', range(1, 23))
        visit_vars.append((f'visit_{i}_city', f'visit_{i}_start_day', f'visit_{i}_duration'))
    
    # Constraint: All cities must be visited exactly once
    def all_cities_visited(*args):
        visited_cities = [args[i*3] for i in range(max_visits)]
        return len(set(visited_cities)) == len(cities) and set(visited_cities) == set(cities)
    
    problem.addConstraint(all_cities_visited, [var[0] for var in visit_vars])
    
    # Constraint: Visits must not overlap and must be in chronological order
    def chronological_order(*args):
        for i in range(max_visits - 1):
            current_start = args[i*3 + 1]
            current_duration = args[i*3 + 2]
            next_start = args[(i+1)*3 + 1]
            
            if current_start + current_duration > next_start:
                return False
        return True
    
    problem.addConstraint(chronological_order, [var for visit in visit_vars for var in visit])
    
    # Constraint: Total days must be 23
    def total_days_23(*args):
        total = 0
        for i in range(max_visits):
            total += args[i*3 + 2]
        return total == 23
    
    problem.addConstraint(total_days_23, [var for visit in visit_vars for var in visit])
    
    # Constraint: Each city must have the required number of days
    def required_days_constraint(*args):
        city_days = {}
        for i in range(max_visits):
            city = args[i*3]
            duration = args[i*3 + 2]
            city_days[city] = city_days.get(city, 0) + duration
        
        for city, required in required_days.items():
            if city_days.get(city, 0) != required:
                return False
        return True
    
    problem.addConstraint(required_days_constraint, [var for visit in visit_vars for var in visit])
    
    # Constraint: Direct flights between consecutive cities
    def valid_flights(*args):
        for i in range(max_visits - 1):
            current_city = args[i*3]
            next_city = args[(i+1)*3]
            
            if next_city not in flight_connections.get(current_city, set()):
                return False
        return True
    
    problem.addConstraint(valid_flights, [var[0] for var in visit_vars])
    
    # Special constraints for Amsterdam and Berlin
    def amsterdam_constraint(*args):
        for i in range(max_visits):
            city = args[i*3]
            start_day = args[i*3 + 1]
            duration = args[i*3 + 2]
            
            if city == 'Amsterdam':
                # Amsterdam visit must include days 5-8
                amsterdam_days = set(range(start_day, start_day + duration))
                required_amsterdam_days = set(range(5, 9))  # Days 5-8
                if not required_amsterdam_days.issubset(amsterdam_days):
                    return False
        return True
    
    problem.addConstraint(amsterdam_constraint, [var for visit in visit_vars for var in visit])
    
    def berlin_constraint(*args):
        for i in range(max_visits):
            city = args[i*3]
            start_day = args[i*3 + 1]
            duration = args[i*3 + 2]
            
            if city == 'Berlin':
                # Berlin visit must include days 16-19
                berlin_days = set(range(start_day, start_day + duration))
                required_berlin_days = set(range(16, 20))  # Days 16-19
                if not required_berlin_days.issubset(berlin_days):
                    return False
        return True
    
    problem.addConstraint(berlin_constraint, [var for visit in visit_vars for var in visit])
    
    def reykjavik_constraint(*args):
        for i in range(max_visits):
            city = args[i*3]
            start_day = args[i*3 + 1]
            duration = args[i*3 + 2]
            
            if city == 'Reykjavik':
                # Reykjavik visit must include days 12-16
                reykjavik_days = set(range(start_day, start_day + duration))
                required_reykjavik_days = set(range(12, 17))  # Days 12-16
                if not required_reykjavik_days.issubset(reykjavik_days):
                    return False
        return True
    
    problem.addConstraint(reykjavik_constraint, [var for visit in visit_vars for var in visit])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Build the itinerary
    itinerary = []
    visits = []
    
    for i in range(max_visits):
        city = solution[f'visit_{i}_city']
        start_day = solution[f'visit_{i}_start_day']
        duration = solution[f'visit_{i}_duration']
        visits.append((city, start_day, duration))
    
    # Sort visits by start day
    visits.sort(key=lambda x: x[1])
    
    for city, start_day, duration in visits:
        end_day = start_day + duration - 1
        if start_day == end_day:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
    
    # Output the result
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()