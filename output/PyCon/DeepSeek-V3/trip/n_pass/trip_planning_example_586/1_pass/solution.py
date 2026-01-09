import json
from constraint import Problem, AllDifferentConstraint

def solve_trip_plan():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = ["Frankfurt", "Naples", "Helsinki", "Lyon", "Prague"]
    required_days = {
        "Frankfurt": 3,
        "Naples": 4,
        "Helsinki": 4,
        "Lyon": 3,
        "Prague": 2
    }
    
    # Direct flight connections
    direct_flights = [
        ("Prague", "Lyon"),
        ("Prague", "Frankfurt"), 
        ("Frankfurt", "Lyon"),
        ("Helsinki", "Naples"),
        ("Helsinki", "Frankfurt"),
        ("Naples", "Frankfurt"),
        ("Prague", "Helsinki")
    ]
    
    # Create bidirectional connections
    connections = {}
    for city1, city2 in direct_flights:
        if city1 not in connections:
            connections[city1] = []
        if city2 not in connections:
            connections[city2] = []
        connections[city1].append(city2)
        connections[city2].append(city1)
    
    # Total days
    total_days = 12
    
    # Variables: day_i represents the city visited on day i (1-indexed)
    for day in range(1, total_days + 1):
        problem.addVariable(f"day_{day}", cities)
    
    # Constraint 1: Total days in each city must match requirements
    for city in cities:
        problem.addConstraint(
            lambda *days, city=city, req=required_days[city]: 
            sum(1 for d in days if d == city) == req,
            [f"day_{i}" for i in range(1, total_days + 1)]
        )
    
    # Constraint 2: Helsinki must be visited from day 2 to day 5 (inclusive)
    for day in [2, 3, 4, 5]:
        problem.addConstraint(lambda city: city == "Helsinki", [f"day_{day}"])
    
    # Constraint 3: Prague must be visited on day 1 or day 2 (workshop constraint)
    problem.addConstraint(
        lambda day1, day2: day1 == "Prague" or day2 == "Prague",
        ["day_1", "day_2"]
    )
    
    # Constraint 4: Travel only between connected cities
    for day in range(1, total_days):
        problem.addConstraint(
            lambda city1, city2: city1 == city2 or city2 in connections.get(city1, []),
            [f"day_{day}", f"day_{day+1}"]
        )
    
    # Find a solution
    solution = problem.getSolution()
    
    if not solution:
        return {"error": "No valid itinerary found"}
    
    # Convert solution to itinerary format
    itinerary = []
    current_city = solution["day_1"]
    start_day = 1
    
    for day in range(2, total_days + 1):
        if solution[f"day_{day}"] != current_city:
            # End of stay in current city
            end_day = day - 1
            if start_day == end_day:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{end_day}"
            itinerary.append({"day_range": day_range, "place": current_city})
            
            # Start new stay
            current_city = solution[f"day_{day}"]
            start_day = day
    
    # Add the last stay
    if start_day == total_days:
        day_range = f"Day {start_day}"
    else:
        day_range = f"Day {start_day}-{total_days}"
    itinerary.append({"day_range": day_range, "place": current_city})
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_trip_plan()
    print(json.dumps(result, indent=2))