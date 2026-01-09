import json
from constraint import Problem

def main():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = ["Madrid", "Dublin", "Tallinn"]
    required_days = {"Madrid": 4, "Dublin": 3, "Tallinn": 2}
    
    # Direct flight connections
    direct_flights = [("Madrid", "Dublin"), ("Dublin", "Tallinn")]
    
    # Days are numbered 1 to 7
    days = list(range(1, 8))
    
    # Variables: for each day, which city we're in
    problem.addVariables(days, cities)
    
    # Constraint: total days in each city must match requirements
    for city in cities:
        problem.addConstraint(lambda *assignments, c=city: assignments.count(c) == required_days[c], days)
    
    # Constraint: can only travel between cities with direct flights
    def valid_transition(day1_city, day2_city):
        if day1_city == day2_city:
            return True
        return (day1_city, day2_city) in direct_flights or (day2_city, day1_city) in direct_flights
    
    for i in range(1, 7):
        problem.addConstraint(valid_transition, [i, i+1])
    
    # Constraint: Tallinn workshop between day 6 and day 7
    # This means we must be in Tallinn on both day 6 and day 7
    problem.addConstraint(lambda day6: day6 == "Tallinn", [6])
    problem.addConstraint(lambda day7: day7 == "Tallinn", [7])
    
    # Find a solution
    solution = problem.getSolution()
    
    if not solution:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Convert the solution to the required itinerary format
    itinerary = []
    current_city = solution[1]
    start_day = 1
    
    for day in range(2, 8):
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
    if start_day == 7:
        day_range = f"Day {start_day}"
    else:
        day_range = f"Day {start_day}-7"
    itinerary.append({"day_range": day_range, "place": current_city})
    
    # Output the result
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()