import json
from constraint import Problem, AllDifferentConstraint

def solve_itinerary():
    problem = Problem()
    
    # Define cities and their required days
    cities = ["Hamburg", "Munich", "Manchester", "Lyon", "Split"]
    required_days = {
        "Hamburg": 7,
        "Munich": 6, 
        "Manchester": 2,
        "Lyon": 2,
        "Split": 7
    }
    
    # Define direct flight connections (bidirectional)
    connections = {
        "Split": ["Munich", "Lyon", "Hamburg", "Manchester"],
        "Munich": ["Split", "Manchester", "Hamburg", "Lyon"],
        "Manchester": ["Munich", "Hamburg", "Split"],
        "Hamburg": ["Manchester", "Munich", "Split"],
        "Lyon": ["Split", "Munich"]
    }
    
    # Define special constraints
    # Manchester must be visited between day 19-20 (inclusive)
    # Lyon must be visited on day 13-14 (inclusive)
    
    # We'll model this as finding the order of cities and their durations
    # Since we have 5 cities and 20 days, we need to find the sequence
    
    # Approach: Find permutations of city visits that satisfy constraints
    total_days = 20
    
    # Variables: sequence of cities and their start days
    # We'll use a different approach - find the order and durations
    
    # Let's create variables for the visit order
    num_cities = len(cities)
    problem.addVariables(range(num_cities), cities)
    problem.addConstraint(AllDifferentConstraint(), range(num_cities))
    
    # Add duration variables for each city position
    durations = [f"dur_{i}" for i in range(num_cities)]
    problem.addVariables(durations, range(1, total_days - num_cities + 2))
    
    # Constraint: total days must equal 20
    def total_days_constraint(*args):
        city_order = args[:num_cities]
        dur_values = args[num_cities:]
        
        # Check if durations match required days for each city
        city_days = {}
        for city, days in zip(city_order, dur_values):
            city_days[city] = city_days.get(city, 0) + days
        
        for city, req_days in required_days.items():
            if city_days.get(city, 0) != req_days:
                return False
        
        return True
    
    problem.addConstraint(total_days_constraint, list(range(num_cities)) + durations)
    
    # Constraint: consecutive cities must be connected by direct flights
    def flight_constraint(*args):
        city_order = args[:num_cities]
        
        for i in range(len(city_order) - 1):
            city1 = city_order[i]
            city2 = city_order[i + 1]
            if city2 not in connections[city1]:
                return False
        return True
    
    problem.addConstraint(flight_constraint, list(range(num_cities)))
    
    # Constraint: Manchester must include day 19-20
    def manchester_constraint(*args):
        city_order = args[:num_cities]
        dur_values = args[num_cities:]
        
        # Calculate day ranges for each visit
        current_day = 1
        manchester_found = False
        
        for i, (city, days) in enumerate(zip(city_order, dur_values)):
            end_day = current_day + days - 1
            if city == "Manchester":
                # Check if Manchester covers day 19-20
                if current_day <= 19 and end_day >= 20:
                    manchester_found = True
            current_day = end_day + 1
        
        return manchester_found
    
    problem.addConstraint(manchester_constraint, list(range(num_cities)) + durations)
    
    # Constraint: Lyon must include day 13-14
    def lyon_constraint(*args):
        city_order = args[:num_cities]
        dur_values = args[num_cities:]
        
        current_day = 1
        lyon_found = False
        
        for i, (city, days) in enumerate(zip(city_order, dur_values)):
            end_day = current_day + days - 1
            if city == "Lyon":
                # Check if Lyon covers day 13-14
                if current_day <= 13 and end_day >= 14:
                    lyon_found = True
            current_day = end_day + 1
        
        return lyon_found
    
    problem.addConstraint(lyon_constraint, list(range(num_cities)) + durations)
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first solution
    solution = solutions[0]
    
    # Build the itinerary
    itinerary = []
    current_day = 1
    
    for i in range(num_cities):
        city = solution[i]
        duration = solution[f"dur_{i}"]
        end_day = current_day + duration - 1
        
        if duration > 0:  # Only add if duration is positive
            day_range = f"Day {current_day}-{end_day}" if duration > 1 else f"Day {current_day}"
            itinerary.append({
                "day_range": day_range,
                "place": city
            })
        
        current_day = end_day + 1
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))