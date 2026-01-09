import json
from constraint import Problem, AllDifferentConstraint

def solve_trip_plan():
    # Initialize constraint problem
    problem = Problem()
    
    # Cities and their required days
    cities = {
        'Dubrovnik': 5,
        'Warsaw': 2,
        'Stuttgart': 7,
        'Bucharest': 6,
        'Copenhagen': 3
    }
    
    # Direct flight connections
    flights = {
        'Warsaw': ['Copenhagen', 'Stuttgart', 'Bucharest'],
        'Copenhagen': ['Warsaw', 'Stuttgart', 'Bucharest', 'Dubrovnik'],
        'Stuttgart': ['Warsaw', 'Copenhagen'],
        'Bucharest': ['Warsaw', 'Copenhagen'],
        'Dubrovnik': ['Copenhagen']
    }
    
    # Make flight connections bidirectional
    for city in list(flights.keys()):
        for connected_city in flights[city]:
            if city not in flights[connected_city]:
                flights[connected_city].append(city)
    
    # Total days
    total_days = 19
    
    # Conference and wedding constraints
    conference_days = [7, 13]
    wedding_days = list(range(1, 7))  # Days 1-6
    
    # Create variables for each day (1 to 19)
    days = list(range(1, total_days + 1))
    
    # Add variables: each day has a city
    problem.addVariables(days, list(cities.keys()))
    
    # Conference constraint: must be in Stuttgart on days 7 and 13
    problem.addConstraint(lambda city: city == 'Stuttgart', [7])
    problem.addConstraint(lambda city: city == 'Stuttgart', [13])
    
    # Wedding constraint: must be in Bucharest on days 1-6
    for day in wedding_days:
        problem.addConstraint(lambda city: city == 'Bucharest', [day])
    
    # Constraint: consecutive days in same city form continuous stays
    def consecutive_constraint(*day_cities):
        for i in range(len(day_cities) - 1):
            if day_cities[i] != day_cities[i + 1]:
                # Check if flight exists between the two cities
                if day_cities[i + 1] not in flights[day_cities[i]]:
                    return False
        return True
    
    problem.addConstraint(consecutive_constraint, days)
    
    # Constraint: total days in each city must match requirements
    def city_day_constraint(*day_assignments):
        city_counts = {city: 0 for city in cities}
        for city in day_assignments:
            city_counts[city] += 1
        
        for city, required_days in cities.items():
            if city_counts[city] != required_days:
                return False
        return True
    
    problem.addConstraint(city_day_constraint, days)
    
    # Find a solution
    solution = problem.getSolution()
    
    if not solution:
        return {"error": "No valid itinerary found"}
    
    # Convert solution to itinerary format
    itinerary = []
    current_city = solution[1]
    start_day = 1
    
    for day in range(2, total_days + 1):
        if solution[day] != current_city:
            # End of current stay
            if start_day == day - 1:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{day - 1}"
            itinerary.append({"day_range": day_range, "place": current_city})
            current_city = solution[day]
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