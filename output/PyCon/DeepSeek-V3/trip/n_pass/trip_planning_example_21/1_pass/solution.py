import json
from constraint import Problem

def main():
    # Define the problem parameters
    total_days = 10
    cities = ['Mykonos', 'Vienna', 'Venice']
    
    # Duration requirements
    venice_days = 6
    mykonos_days = 2
    vienna_days = 4
    
    # Workshop constraint: Venice between day 5 and day 10
    workshop_start_day = 5
    workshop_end_day = 10
    
    # Direct flight connections
    direct_flights = {
        'Mykonos': ['Vienna'],
        'Vienna': ['Mykonos', 'Venice'],
        'Venice': ['Vienna']
    }
    
    # Create constraint problem
    problem = Problem()
    
    # Add variables: each day's location
    days = list(range(1, total_days + 1))
    for day in days:
        problem.addVariable(day, cities)
    
    # Constraint 1: Total days in each city must match requirements
    def days_in_city_constraint(*assignments):
        location_count = {city: 0 for city in cities}
        for location in assignments:
            location_count[location] += 1
        
        return (location_count['Venice'] == venice_days and
                location_count['Mykonos'] == mykonos_days and
                location_count['Vienna'] == vienna_days)
    
    problem.addConstraint(days_in_city_constraint, days)
    
    # Constraint 2: Workshop in Venice between day 5 and day 10
    def workshop_constraint(*assignments):
        # Check that from day 5 to day 10, we're always in Venice
        for day in range(workshop_start_day, workshop_end_day + 1):
            if assignments[day - 1] != 'Venice':  # -1 because days list starts from 1
                return False
        return True
    
    problem.addConstraint(workshop_constraint, days)
    
    # Constraint 3: Direct flights only - can only transition between connected cities
    def direct_flight_constraint(day1_city, day2_city):
        if day1_city == day2_city:
            return True  # Staying in same city is always allowed
        return day2_city in direct_flights[day1_city]
    
    for i in range(1, total_days):
        problem.addConstraint(direct_flight_constraint, [i, i + 1])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Take the first solution (all valid solutions should be equivalent for our constraints)
    solution = solutions[0]
    
    # Convert solution to itinerary format
    itinerary = []
    current_city = solution[1]
    start_day = 1
    
    for day in range(2, total_days + 1):
        if solution[day] != current_city:
            # End of stay in current city
            end_day = day - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": current_city
            })
            current_city = solution[day]
            start_day = day
    
    # Add the final stay
    itinerary.append({
        "day_range": f"Day {start_day}-{total_days}",
        "place": current_city
    })
    
    # Output the result
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()