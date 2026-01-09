import json
from constraint import Problem, AllDifferentConstraint

def solve_itinerary():
    problem = Problem()
    
    # Define the cities
    cities = ['Prague', 'Berlin', 'Tallinn', 'Stockholm']
    
    # Define days (1 to 12)
    days = list(range(1, 13))
    
    # Add variables for each day - which city we're in
    problem.addVariables(days, cities)
    
    # Constraint 1: Stay in Prague for exactly 2 days
    def prague_constraint(*assignments):
        return sum(1 for city in assignments if city == 'Prague') == 2
    problem.addConstraint(prague_constraint, days)
    
    # Constraint 2: Stay in Berlin for exactly 3 days
    def berlin_constraint(*assignments):
        return sum(1 for city in assignments if city == 'Berlin') == 3
    problem.addConstraint(berlin_constraint, days)
    
    # Constraint 3: Stay in Tallinn for exactly 5 days
    def tallinn_constraint(*assignments):
        return sum(1 for city in assignments if city == 'Tallinn') == 5
    problem.addConstraint(tallinn_constraint, days)
    
    # Constraint 4: Stay in Stockholm for exactly 5 days
    def stockholm_constraint(*assignments):
        return sum(1 for city in assignments if city == 'Stockholm') == 5
    problem.addConstraint(stockholm_constraint, days)
    
    # Constraint 5: Conference in Berlin on days 6 and 8
    problem.addConstraint(lambda city: city == 'Berlin', [6])
    problem.addConstraint(lambda city: city == 'Berlin', [8])
    
    # Constraint 6: Visit relatives in Tallinn between day 8 and day 12
    # This means from day 9 to day 12, must be in Tallinn
    for day in range(9, 13):
        problem.addConstraint(lambda city: city == 'Tallinn', [day])
    
    # Constraint 7: Direct flight connectivity
    direct_flights = {
        'Berlin': ['Tallinn', 'Stockholm'],
        'Tallinn': ['Berlin', 'Prague', 'Stockholm'],
        'Prague': ['Tallinn', 'Stockholm'],
        'Stockholm': ['Tallinn', 'Prague', 'Berlin']
    }
    
    def flight_constraint(day1_city, day2_city):
        if day1_city == day2_city:
            return True
        return day2_city in direct_flights[day1_city]
    
    for i in range(1, 12):
        problem.addConstraint(flight_constraint, [i, i+1])
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Convert to itinerary format with day ranges
    itinerary = []
    current_city = solution[1]
    start_day = 1
    
    for day in range(2, 13):
        if solution[day] != current_city:
            # End of stay in current city
            if start_day == day - 1:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{day-1}"
            itinerary.append({"day_range": day_range, "place": current_city})
            current_city = solution[day]
            start_day = day
    
    # Add the last stay
    if start_day == 12:
        day_range = f"Day {start_day}"
    else:
        day_range = f"Day {start_day}-12"
    itinerary.append({"day_range": day_range, "place": current_city})
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))