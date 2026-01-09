import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = ["Dublin", "Madrid", "Oslo", "London", "Vilnius", "Berlin"]
    required_days = {
        "Dublin": 3,
        "Madrid": 2, 
        "Oslo": 3,
        "London": 2,
        "Vilnius": 3,
        "Berlin": 5
    }
    
    # Direct flight connections
    direct_flights = [
        ("London", "Madrid"), ("Oslo", "Vilnius"), ("Berlin", "Vilnius"),
        ("Madrid", "Oslo"), ("Madrid", "Dublin"), ("London", "Oslo"),
        ("Madrid", "Berlin"), ("Berlin", "Oslo"), ("Dublin", "Oslo"),
        ("London", "Dublin"), ("London", "Berlin"), ("Berlin", "Dublin")
    ]
    
    # Make flights bidirectional
    bidirectional_flights = set()
    for city1, city2 in direct_flights:
        bidirectional_flights.add((city1, city2))
        bidirectional_flights.add((city2, city1))
    
    # Total days
    total_days = 13
    
    # Define variables for start day of each city visit
    # We'll model this as finding the order of cities to visit
    city_order = range(len(cities))
    problem.addVariables(city_order, range(len(cities)))
    problem.addConstraint(AllDifferentConstraint(), city_order)
    
    # We need to find a sequence of cities that satisfies:
    # 1. Total days = 13
    # 2. Required days for each city
    # 3. Direct flights between consecutive cities
    # 4. Special date constraints
    
    # Let's model this differently - find assignment of days to cities
    day_city_vars = list(range(total_days))
    problem.addVariables(day_city_vars, cities)
    
    # Constraint: each city must be visited for exactly required_days days
    for city in cities:
        problem.addConstraint(lambda *days, city=city: days.count(city) == required_days[city], day_city_vars)
    
    # Constraint: consecutive days in same city or connected by direct flight
    for day in range(total_days - 1):
        problem.addConstraint(
            lambda city1, city2: city1 == city2 or (city1, city2) in bidirectional_flights,
            [day_city_vars[day], day_city_vars[day + 1]]
        )
    
    # Special constraints
    # Dublin between day 7 and day 9 (inclusive, 1-indexed, so days 6-8 in 0-index)
    problem.addConstraint(
        lambda d6, d7, d8: "Dublin" in [d6, d7, d8],
        [day_city_vars[6], day_city_vars[7], day_city_vars[8]]
    )
    
    # Madrid between day 2 and day 3 (1-indexed, so days 1-2 in 0-index)
    problem.addConstraint(
        lambda d1, d2: "Madrid" in [d1, d2],
        [day_city_vars[1], day_city_vars[2]]
    )
    
    # Berlin wedding between day 3 and day 7 (1-indexed, so days 2-6 in 0-index)
    problem.addConstraint(
        lambda d2, d3, d4, d5, d6: "Berlin" in [d2, d3, d4, d5, d6],
        [day_city_vars[2], day_city_vars[3], day_city_vars[4], day_city_vars[5], day_city_vars[6]]
    )
    
    # Find solution
    solutions = problem.getSolutions()
    
    if solutions:
        solution = solutions[0]
        
        # Convert solution to itinerary format
        itinerary = []
        current_city = solution[0]
        start_day = 0
        
        for day in range(1, total_days):
            if solution[day] != current_city:
                # End of stay in current city
                if start_day == day - 1:
                    day_range = f"Day {start_day + 1}"
                else:
                    day_range = f"Day {start_day + 1}-{day}"
                itinerary.append({"day_range": day_range, "place": current_city})
                current_city = solution[day]
                start_day = day
        
        # Add the last stay
        if start_day == total_days - 1:
            day_range = f"Day {start_day + 1}"
        else:
            day_range = f"Day {start_day + 1}-{total_days}"
        itinerary.append({"day_range": day_range, "place": current_city})
        
        # Output as JSON
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"error": "No valid itinerary found"}, indent=2))

if __name__ == "__main__":
    main()