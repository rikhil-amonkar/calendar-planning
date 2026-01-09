import json
from constraint import Problem, AllDifferentConstraint

def solve_trip_plan():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = ['Geneva', 'Munich', 'Valencia', 'Bucharest', 'Stuttgart']
    required_days = {
        'Geneva': 4,
        'Munich': 7,
        'Valencia': 6,
        'Bucharest': 2,
        'Stuttgart': 2
    }
    
    # Total days
    total_days = 17
    
    # Direct flight connections (make bidirectional)
    direct_flights = [
        ('Geneva', 'Munich'),
        ('Munich', 'Valencia'),
        ('Bucharest', 'Valencia'),
        ('Munich', 'Bucharest'),
        ('Valencia', 'Stuttgart'),
        ('Geneva', 'Valencia')
    ]
    
    # Create bidirectional flight connections
    flight_connections = set()
    for city1, city2 in direct_flights:
        flight_connections.add((city1, city2))
        flight_connections.add((city2, city1))
    
    # Variables: order of cities to visit
    problem.addVariables(range(5), cities)
    problem.addConstraint(AllDifferentConstraint())
    
    # Constraint: total days must equal 17
    def total_days_constraint(*order):
        return sum(required_days[city] for city in order) == total_days
    
    problem.addConstraint(total_days_constraint, range(5))
    
    # Constraint: consecutive cities must have direct flights
    def flight_constraint(city1, city2):
        return (city1, city2) in flight_connections
    
    for i in range(4):
        problem.addConstraint(flight_constraint, (i, i+1))
    
    # Geneva must be first (based on problem description)
    def geneva_first(*order):
        return order[0] == 'Geneva'
    
    problem.addConstraint(geneva_first, range(5))
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    order = [solution[i] for i in range(5)]
    
    # Calculate day ranges
    itinerary = []
    current_day = 1
    
    for i, city in enumerate(order):
        days_in_city = required_days[city]
        end_day = current_day + days_in_city - 1
        
        if current_day == end_day:
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