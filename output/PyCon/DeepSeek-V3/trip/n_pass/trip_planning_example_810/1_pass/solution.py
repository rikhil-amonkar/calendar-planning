import json
from constraint import Problem, AllDifferentConstraint

def solve_trip_plan():
    problem = Problem()
    
    # Define cities and their required days
    cities = ['Berlin', 'Nice', 'Athens', 'Stockholm', 'Barcelona', 'Vilnius', 'Lyon']
    required_days = {
        'Berlin': 3,
        'Nice': 5,
        'Athens': 5,
        'Stockholm': 5,
        'Barcelona': 2,
        'Vilnius': 4,
        'Lyon': 2
    }
    
    # Define direct flight connections
    direct_flights = {
        'Lyon': ['Nice'],
        'Stockholm': ['Athens'],
        'Nice': ['Athens', 'Lyon', 'Barcelona', 'Stockholm'],
        'Berlin': ['Athens', 'Nice', 'Barcelona', 'Vilnius', 'Stockholm'],
        'Barcelona': ['Nice', 'Athens', 'Stockholm', 'Lyon', 'Berlin'],
        'Athens': ['Stockholm', 'Nice', 'Berlin', 'Vilnius', 'Barcelona'],
        'Vilnius': ['Berlin', 'Athens']
    }
    
    # Create variables for visit order (position in itinerary)
    positions = list(range(len(cities)))
    problem.addVariables(cities, positions)
    problem.addConstraint(AllDifferentConstraint(), cities)
    
    # Total days constraint
    total_days = 20
    problem.addConstraint(lambda *durations: sum(durations) == total_days, 
                         list(required_days.values()))
    
    # Berlin constraints: 3 days with conference on day 1 and day 3
    def berlin_constraint(berlin_pos):
        return berlin_pos == 0  # Berlin must be first
    
    problem.addConstraint(berlin_constraint, ['Berlin'])
    
    # Barcelona constraints: workshop between day 3 and day 4
    def barcelona_constraint(barcelona_pos, berlin_days):
        # Barcelona must be visited right after Berlin (day 3-4)
        return barcelona_pos == 1
    
    problem.addConstraint(barcelona_constraint, ['Barcelona', 'Berlin'])
    
    # Lyon constraints: wedding between day 4 and day 5
    def lyon_constraint(lyon_pos, barcelona_days):
        # Lyon must be visited right after Barcelona
        return lyon_pos == 2
    
    problem.addConstraint(lyon_constraint, ['Lyon', 'Barcelona'])
    
    # Flight connectivity constraints
    def flight_connectivity(*city_positions):
        city_order = sorted([(pos, city) for city, pos in zip(cities, city_positions)])
        
        for i in range(len(city_order) - 1):
            current_city = city_order[i][1]
            next_city = city_order[i + 1][1]
            
            if next_city not in direct_flights.get(current_city, []):
                return False
        
        return True
    
    problem.addConstraint(flight_connectivity, cities)
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Create ordered list of cities by position
    ordered_cities = sorted([(pos, city) for city, pos in solution.items()])
    
    # Build itinerary with day ranges
    itinerary = []
    current_day = 1
    
    for pos, city in ordered_cities:
        days_needed = required_days[city]
        end_day = current_day + days_needed - 1
        
        if days_needed == 1:
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