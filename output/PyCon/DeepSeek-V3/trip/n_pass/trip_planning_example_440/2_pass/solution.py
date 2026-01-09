import json
from constraint import Problem

def main():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = ["Split", "Helsinki", "Reykjavik", "Vilnius", "Geneva"]
    required_days = {
        "Split": 2,
        "Helsinki": 2, 
        "Reykjavik": 3,
        "Vilnius": 3,
        "Geneva": 6
    }
    
    # Direct flight connections
    direct_flights = [
        ("Split", "Helsinki"),
        ("Geneva", "Split"),
        ("Geneva", "Helsinki"),
        ("Helsinki", "Reykjavik"),
        ("Vilnius", "Helsinki"),
        ("Split", "Vilnius")
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
    
    # Variables: for each day (1-12), which city are we in
    days = list(range(1, 13))
    for day in days:
        problem.addVariable(f"day_{day}", cities)
    
    # Constraint 1: Total days in each city must match requirements
    def total_days_constraint(*assignments):
        day_assignments = assignments
        city_counts = {city: 0 for city in cities}
        
        for city in day_assignments:
            city_counts[city] += 1
        
        for city, required in required_days.items():
            if city_counts[city] != required:
                return False
        
        return True
    
    problem.addConstraint(total_days_constraint, [f"day_{day}" for day in days])
    
    # Constraint 2: Can only travel between connected cities on consecutive days
    def travel_constraint(day1_city, day2_city):
        if day1_city == day2_city:
            return True
        return day2_city in connections.get(day1_city, set())
    
    for i in range(1, 12):
        problem.addConstraint(travel_constraint, [f"day_{i}", f"day_{i+1}"])
    
    # Constraint 3: Wedding in Reykjavik on at least one day between 10-12
    def wedding_constraint(day10, day11, day12):
        return "Reykjavik" in [day10, day11, day12]
    
    problem.addConstraint(wedding_constraint, ["day_10", "day_11", "day_12"])
    
    # Constraint 4: Relatives in Vilnius on at least one day between 7-9
    def relatives_constraint(day7, day8, day9):
        return "Vilnius" in [day7, day8, day9]
    
    problem.addConstraint(relatives_constraint, ["day_7", "day_8", "day_9"])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    solution = solutions[0]
    
    # Convert solution to itinerary format
    itinerary = []
    current_city = solution["day_1"]
    start_day = 1
    
    for day in range(2, 13):
        if solution[f"day_{day}"] != current_city:
            if start_day == day - 1:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{day-1}"
            itinerary.append({"day_range": day_range, "place": current_city})
            current_city = solution[f"day_{day}"]
            start_day = day
    
    # Add the last segment
    if start_day == 12:
        day_range = f"Day {start_day}"
    else:
        day_range = f"Day {start_day}-12"
    itinerary.append({"day_range": day_range, "place": current_city})
    
    # Output as JSON
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()