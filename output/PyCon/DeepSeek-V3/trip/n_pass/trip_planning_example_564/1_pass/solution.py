import json
from constraint import Problem, AllDifferentConstraint

def solve_trip_plan():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = ['Istanbul', 'Rome', 'Seville', 'Naples', 'Santorini']
    required_days = {
        'Istanbul': 2,
        'Rome': 3,
        'Seville': 4,
        'Naples': 7,
        'Santorini': 4
    }
    
    # Direct flight connections
    direct_flights = [
        ('Rome', 'Santorini'),
        ('Seville', 'Rome'),
        ('Istanbul', 'Naples'),
        ('Naples', 'Santorini'),
        ('Rome', 'Naples'),
        ('Rome', 'Istanbul')
    ]
    
    # Create bidirectional connections
    connections = {}
    for city1, city2 in direct_flights:
        if city1 not in connections:
            connections[city1] = set()
        if city2 not in connections:
            connections[city2] = set()
        connections[city1].add(city2)
        connections[city2].add(city1)
    
    # Total days
    total_days = 16
    
    # Define variables for visit order
    problem.addVariables(['city1', 'city2', 'city3', 'city4', 'city5'], cities)
    problem.addConstraint(AllDifferentConstraint())
    
    # Define duration variables for each city visit
    problem.addVariables(['dur1', 'dur2', 'dur3', 'dur4', 'dur5'], range(1, total_days + 1))
    
    # Total days constraint
    def total_days_constraint(d1, d2, d3, d4, d5):
        return d1 + d2 + d3 + d4 + d5 == total_days
    
    problem.addConstraint(total_days_constraint, ['dur1', 'dur2', 'dur3', 'dur4', 'dur5'])
    
    # Required days constraint
    def required_days_constraint(c1, c2, c3, c4, c5, d1, d2, d3, d4, d5):
        days_allocated = {}
        days_allocated[c1] = days_allocated.get(c1, 0) + d1
        days_allocated[c2] = days_allocated.get(c2, 0) + d2
        days_allocated[c3] = days_allocated.get(c3, 0) + d3
        days_allocated[c4] = days_allocated.get(c4, 0) + d4
        days_allocated[c5] = days_allocated.get(c5, 0) + d5
        
        for city, required in required_days.items():
            if days_allocated.get(city, 0) != required:
                return False
        return True
    
    problem.addConstraint(required_days_constraint, 
                         ['city1', 'city2', 'city3', 'city4', 'city5', 
                          'dur1', 'dur2', 'dur3', 'dur4', 'dur5'])
    
    # Flight connection constraints
    def flight_constraint(c1, c2, c3, c4, c5):
        cities_order = [c1, c2, c3, c4, c5]
        for i in range(len(cities_order) - 1):
            current_city = cities_order[i]
            next_city = cities_order[i + 1]
            if next_city not in connections.get(current_city, set()):
                return False
        return True
    
    problem.addConstraint(flight_constraint, ['city1', 'city2', 'city3', 'city4', 'city5'])
    
    # Special constraints
    def istanbul_constraint(c1, c2, c3, c4, c5, d1, d2, d3, d4):
        cities_order = [c1, c2, c3, c4, c5]
        durations = [d1, d2, d3, d4, 0]  # d5 is not needed for this calculation
        
        # Find Istanbul position and calculate day ranges
        current_day = 1
        for i, city in enumerate(cities_order):
            duration = durations[i]
            if city == 'Istanbul':
                # Istanbul must be visited between day 6 and day 7
                # This means it should start on day 6 or earlier and end on day 7 or later
                start_day = current_day
                end_day = current_day + duration - 1
                if not (start_day <= 6 and end_day >= 7):
                    return False
            current_day += duration
        return True
    
    def santorini_constraint(c1, c2, c3, c4, c5, d1, d2, d3, d4, d5):
        cities_order = [c1, c2, c3, c4, c5]
        durations = [d1, d2, d3, d4, d5]
        
        # Find Santorini position and calculate day ranges
        current_day = 1
        for i, city in enumerate(cities_order):
            duration = durations[i]
            if city == 'Santorini':
                # Santorini wedding between day 13 and 16
                start_day = current_day
                end_day = current_day + duration - 1
                if not (start_day <= 13 and end_day >= 16):
                    return False
            current_day += duration
        return True
    
    problem.addConstraint(istanbul_constraint, ['city1', 'city2', 'city3', 'city4', 'city5', 'dur1', 'dur2', 'dur3', 'dur4'])
    problem.addConstraint(santorini_constraint, ['city1', 'city2', 'city3', 'city4', 'city5', 'dur1', 'dur2', 'dur3', 'dur4', 'dur5'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Build the itinerary
    itinerary = []
    current_day = 1
    
    for i in range(1, 6):
        city = solution[f'city{i}']
        duration = solution[f'dur{i}']
        end_day = current_day + duration - 1
        
        if duration == 1:
            day_range = f"Day {current_day}"
        else:
            day_range = f"Day {current_day}-{end_day}"
        
        itinerary.append({
            "day_range": day_range,
            "place": city
        })
        
        current_day = end_day + 1
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_trip_plan()
    print(json.dumps(result, indent=2))