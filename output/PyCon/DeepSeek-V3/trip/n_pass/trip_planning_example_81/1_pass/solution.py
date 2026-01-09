import json
from constraint import Problem

def main():
    # Define the problem
    problem = Problem()
    
    # Cities
    cities = ['Mykonos', 'Budapest', 'Hamburg']
    
    # Days (1-9)
    days = list(range(1, 10))
    
    # Add variables: each day has a city
    problem.addVariables(days, cities)
    
    # Constraints
    
    # 1. Mykonos must be visited for exactly 6 days
    problem.addConstraint(lambda *assignments: assignments.count('Mykonos') == 6, days)
    
    # 2. Budapest must be visited for exactly 3 days
    problem.addConstraint(lambda *assignments: assignments.count('Budapest') == 3, days)
    
    # 3. Hamburg must be visited for exactly 2 days
    problem.addConstraint(lambda *assignments: assignments.count('Hamburg') == 2, days)
    
    # 4. Conference days: must be in Mykonos on days 4 and 9
    problem.addConstraint(lambda city: city == 'Mykonos', [4])
    problem.addConstraint(lambda city: city == 'Mykonos', [9])
    
    # 5. Flight constraints: only direct flights allowed
    #    Direct flights exist between: Budapest-Mykonos, Hamburg-Budapest
    #    No direct flight between Hamburg-Mykonos
    def valid_transition(day1_city, day2_city):
        if day1_city == day2_city:
            return True
        flights = {('Budapest', 'Mykonos'), ('Mykonos', 'Budapest'), 
                  ('Hamburg', 'Budapest'), ('Budapest', 'Hamburg')}
        return (day1_city, day2_city) in flights
    
    for i in range(1, 9):
        problem.addConstraint(valid_transition, [i, i+1])
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        result = {"error": "No valid itinerary found"}
        print(json.dumps(result))
        return
    
    # Convert solution to itinerary format
    solution = solutions[0]
    
    # Group consecutive days in the same city
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
            
            # Start new stay
            current_city = solution[day]
            start_day = day
    
    # Add the last stay
    if start_day == 9:
        day_range = f"Day {start_day}"
    else:
        day_range = f"Day {start_day}-9"
    itinerary.append({"day_range": day_range, "place": current_city})
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()