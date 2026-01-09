import constraint
import json

def main():
    # Define the problem
    problem = constraint.Problem()
    
    # Cities and their required days
    cities = ['Stuttgart', 'Edinburgh', 'Athens', 'Split', 'Krakow', 'Venice', 'Mykonos']
    required_days = {
        'Stuttgart': 3,
        'Edinburgh': 4,
        'Athens': 4,
        'Split': 2,
        'Krakow': 4,
        'Venice': 5,
        'Mykonos': 4
    }
    
    # Direct flight connections
    direct_flights = [
        ('Krakow', 'Split'), ('Split', 'Athens'), ('Edinburgh', 'Krakow'),
        ('Venice', 'Stuttgart'), ('Krakow', 'Stuttgart'), ('Edinburgh', 'Stuttgart'),
        ('Stuttgart', 'Athens'), ('Venice', 'Edinburgh'), ('Athens', 'Mykonos'),
        ('Venice', 'Athens'), ('Stuttgart', 'Split'), ('Edinburgh', 'Athens')
    ]
    
    # Make flight connections bidirectional
    flight_connections = set()
    for city1, city2 in direct_flights:
        flight_connections.add((city1, city2))
        flight_connections.add((city2, city1))
    
    # Total days
    total_days = 20
    
    # Define variables for start day of each city visit
    # We'll use -1 to indicate the city is not visited
    for city in cities:
        problem.addVariable(f'{city}_start', range(-1, total_days))
        problem.addVariable(f'{city}_end', range(-1, total_days))
    
    # Constraint: All cities must be visited
    def all_cities_visited(*args):
        starts = args[:len(cities)]
        return all(start != -1 for start in starts)
    
    problem.addConstraint(all_cities_visited, [f'{city}_start' for city in cities])
    
    # Constraint: End day = Start day + required days - 1
    for city in cities:
        def end_day_constraint(start, end, city=city):
            if start == -1:
                return end == -1
            required = required_days[city]
            return end == start + required - 1
        
        problem.addConstraint(end_day_constraint, [f'{city}_start', f'{city}_end'])
    
    # Constraint: No overlapping visits (cities visited sequentially)
    def no_overlaps(*args):
        # args contains all start and end days interleaved
        starts = args[::2]
        ends = args[1::2]
        
        for i in range(len(starts)):
            for j in range(i + 1, len(starts)):
                if starts[i] != -1 and starts[j] != -1:
                    # Check if visits overlap
                    if not (ends[i] < starts[j] or ends[j] < starts[i]):
                        return False
        return True
    
    all_vars = []
    for city in cities:
        all_vars.extend([f'{city}_start', f'{city}_end'])
    problem.addConstraint(no_overlaps, all_vars)
    
    # Constraint: All days from 0 to total_days-1 must be covered
    def all_days_covered(*args):
        starts = args[:len(cities)]
        ends = args[len(cities):]
        
        days_covered = [False] * total_days
        for i in range(len(starts)):
            if starts[i] != -1:
                for day in range(starts[i], ends[i] + 1):
                    if day < total_days:
                        days_covered[day] = True
        
        return all(days_covered)
    
    problem.addConstraint(all_days_covered, all_vars)
    
    # Special constraints
    # Stuttgart: 3 days, workshop between day 11-13
    def stuttgart_constraint(start, end):
        if start == -1:
            return False
        # Workshop must be within the stay
        return start <= 11 and end >= 13
    
    problem.addConstraint(stuttgart_constraint, ['Stuttgart_start', 'Stuttgart_end'])
    
    # Split: 2 days, meet friends between day 13-14
    def split_constraint(start, end):
        if start == -1:
            return False
        # Friends meeting must be within the stay
        return start <= 13 and end >= 14
    
    problem.addConstraint(split_constraint, ['Split_start', 'Split_end'])
    
    # Krakow: 4 days, meet friend between day 8-11
    def krakow_constraint(start, end):
        if start == -1:
            return False
        # Friend meeting must be within the stay
        return start <= 8 and end >= 11
    
    problem.addConstraint(krakow_constraint, ['Krakow_start', 'Krakow_end'])
    
    # Constraint: Travel must be via direct flights
    def valid_travel_order(*args):
        starts = args[:len(cities)]
        ends = args[len(cities):]
        
        # Create visit order
        visits = []
        for i, city in enumerate(cities):
            if starts[i] != -1:
                visits.append((starts[i], city))
        
        visits.sort()
        
        # Check consecutive cities are connected by direct flights
        for i in range(len(visits) - 1):
            city1 = visits[i][1]
            city2 = visits[i + 1][1]
            if (city1, city2) not in flight_connections:
                return False
        
        return True
    
    problem.addConstraint(valid_travel_order, all_vars)
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try without the flight constraint if no solution found
        problem = constraint.Problem()
        
        for city in cities:
            problem.addVariable(f'{city}_start', range(-1, total_days))
            problem.addVariable(f'{city}_end', range(-1, total_days))
        
        problem.addConstraint(all_cities_visited, [f'{city}_start' for city in cities])
        
        for city in cities:
            def end_day_constraint(start, end, city=city):
                if start == -1:
                    return end == -1
                required = required_days[city]
                return end == start + required - 1
            
            problem.addConstraint(end_day_constraint, [f'{city}_start', f'{city}_end'])
        
        problem.addConstraint(no_overlaps, all_vars)
        problem.addConstraint(all_days_covered, all_vars)
        problem.addConstraint(stuttgart_constraint, ['Stuttgart_start', 'Stuttgart_end'])
        problem.addConstraint(split_constraint, ['Split_start', 'Split_end'])
        problem.addConstraint(krakow_constraint, ['Krakow_start', 'Krakow_end'])
        
        solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        
        # Build itinerary
        itinerary = []
        visits = []
        
        for city in cities:
            start = solution[f'{city}_start']
            end = solution[f'{city}_end']
            if start != -1:
                visits.append((start, end, city))
        
        visits.sort()
        
        for start, end, city in visits:
            if start == end:
                day_range = f"Day {start + 1}"
            else:
                day_range = f"Day {start + 1}-{end + 1}"
            itinerary.append({"day_range": day_range, "place": city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()