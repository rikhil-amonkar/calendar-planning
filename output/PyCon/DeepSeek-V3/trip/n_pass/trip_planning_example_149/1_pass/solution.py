import json
from constraint import Problem

def main():
    # Define the problem parameters
    total_days = 10
    cities = ['London', 'Santorini', 'Istanbul']
    
    # Define constraints
    london_days = 3
    santorini_days = 6
    istanbul_days = 3
    
    # Conference days (1-indexed)
    conference_days = [5, 10]
    
    # Direct flight connections
    direct_flights = {
        'London': ['Istanbul', 'Santorini'],
        'Santorini': ['London'],
        'Istanbul': ['London']
    }
    
    # Create constraint problem
    problem = Problem()
    
    # Add variables: each day's location (1-indexed days)
    days = range(1, total_days + 1)
    for day in days:
        problem.addVariable(f'day_{day}', cities)
    
    # Constraint 1: Total days in each city
    def london_constraint(*assignments):
        return sum(1 for city in assignments if city == 'London') == london_days
    
    def santorini_constraint(*assignments):
        return sum(1 for city in assignments if city == 'Santorini') == santorini_days
    
    def istanbul_constraint(*assignments):
        return sum(1 for city in assignments if city == 'Istanbul') == istanbul_days
    
    problem.addConstraint(london_constraint, [f'day_{day}' for day in days])
    problem.addConstraint(santorini_constraint, [f'day_{day}' for day in days])
    problem.addConstraint(istabul_constraint, [f'day_{day}' for day in days])
    
    # Constraint 2: Conference days must be in Santorini
    for conf_day in conference_days:
        problem.addConstraint(lambda x: x == 'Santorini', [f'day_{conf_day}'])
    
    # Constraint 3: Only direct flights allowed between consecutive days
    def flight_constraint(day1_city, day2_city):
        if day1_city == day2_city:
            return True
        return day2_city in direct_flights[day1_city]
    
    for i in range(1, total_days):
        problem.addConstraint(flight_constraint, [f'day_{i}', f'day_{i+1}'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    # Use the first valid solution
    solution = solutions[0]
    
    # Convert solution to itinerary format
    itinerary = []
    current_city = solution['day_1']
    start_day = 1
    
    for day in range(2, total_days + 1):
        if solution[f'day_{day}'] != current_city:
            end_day = day - 1
            itinerary.append({
                "day_range": f"Day {start_day}-{end_day}",
                "place": current_city
            })
            current_city = solution[f'day_{day}']
            start_day = day
    
    # Add the last segment
    itinerary.append({
        "day_range": f"Day {start_day}-{total_days}",
        "place": current_city
    })
    
    # Output the result
    print(json.dumps({"itinerary": itinerary}))

if __name__ == "__main__":
    main()