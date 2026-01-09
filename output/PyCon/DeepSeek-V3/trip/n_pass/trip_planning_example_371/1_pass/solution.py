import json
from constraint import Problem, AllDifferentConstraint

def solve_itinerary():
    problem = Problem()
    
    # Define days and cities
    days = list(range(1, 10))  # Days 1 through 9
    cities = ['Vienna', 'Stockholm', 'Nice', 'Split']
    
    # Add variables: each day has a city
    problem.addVariables(days, cities)
    
    # Constraint 1: Must stay in Nice for exactly 2 days
    problem.addConstraint(lambda *assignments: assignments.count('Nice') == 2, days)
    
    # Constraint 2: Must stay in Stockholm for exactly 5 days
    problem.addConstraint(lambda *assignments: assignments.count('Stockholm') == 5, days)
    
    # Constraint 3: Must stay in Split for exactly 3 days
    problem.addConstraint(lambda *assignments: assignments.count('Split') == 3, days)
    
    # Constraint 4: Must stay in Vienna for exactly 2 days
    problem.addConstraint(lambda *assignments: assignments.count('Vienna') == 2, days)
    
    # Constraint 5: Conference in Split on day 7 and day 9
    problem.addConstraint(lambda day7, day9: day7 == 'Split' and day9 == 'Split', [7, 9])
    
    # Constraint 6: Workshop in Vienna between day 1 and day 2
    # This means Vienna must be visited on day 1 or day 2 (or both)
    problem.addConstraint(lambda day1, day2: day1 == 'Vienna' or day2 == 'Vienna', [1, 2])
    
    # Constraint 7: Direct flights only
    # Define valid transitions between cities
    direct_flights = {
        'Vienna': ['Stockholm', 'Nice', 'Split'],
        'Stockholm': ['Vienna', 'Nice', 'Split'],
        'Nice': ['Vienna', 'Stockholm'],
        'Split': ['Vienna', 'Stockholm']
    }
    
    def valid_transition(day1_city, day2_city):
        if day1_city == day2_city:
            return True  # Staying in same city is always allowed
        return day2_city in direct_flights[day1_city]
    
    # Add transition constraints for consecutive days
    for i in range(1, 9):
        problem.addConstraint(valid_transition, [i, i+1])
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Convert to day ranges format
    itinerary = []
    current_city = solution[1]
    start_day = 1
    
    for day in range(2, 10):
        if solution[day] != current_city:
            # End of current stay
            if start_day == day - 1:
                day_range = f"Day {start_day}"
            else:
                day_range = f"Day {start_day}-{day - 1}"
            itinerary.append({"day_range": day_range, "place": current_city})
            current_city = solution[day]
            start_day = day
    
    # Add the final stay
    if start_day == 9:
        day_range = f"Day {start_day}"
    else:
        day_range = f"Day {start_day}-9"
    itinerary.append({"day_range": day_range, "place": current_city})
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))