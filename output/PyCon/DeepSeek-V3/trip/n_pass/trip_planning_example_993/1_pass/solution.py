import constraint
import json

def main():
    problem = constraint.Problem()
    
    cities = ['Riga', 'Frankfurt', 'Amsterdam', 'Vilnius', 'London', 'Stockholm', 'Bucharest']
    
    # Define the required days for each city
    required_days = {
        'Riga': 2,
        'Frankfurt': 3,
        'Amsterdam': 2,
        'Vilnius': 5,
        'London': 2,
        'Stockholm': 3,
        'Bucharest': 4
    }
    
    # Define direct flight connections
    direct_flights = {
        'London': ['Amsterdam', 'Bucharest', 'Frankfurt', 'Stockholm'],
        'Amsterdam': ['London', 'Stockholm', 'Frankfurt', 'Riga', 'Bucharest', 'Vilnius'],
        'Vilnius': ['Frankfurt', 'Riga', 'Amsterdam'],
        'Riga': ['Vilnius', 'Stockholm', 'Frankfurt', 'Amsterdam', 'Bucharest'],
        'Frankfurt': ['Vilnius', 'Amsterdam', 'Stockholm', 'Riga', 'Bucharest', 'London'],
        'Stockholm': ['Riga', 'Amsterdam', 'Frankfurt', 'London'],
        'Bucharest': ['London', 'Riga', 'Amsterdam', 'Frankfurt']
    }
    
    # Variables: day_i represents the city visited on day i (1-15)
    for day in range(1, 16):
        problem.addVariable(f'day_{day}', cities)
    
    # Constraint 1: Total days in each city must match requirements
    for city in cities:
        problem.addConstraint(
            lambda *days, city=city, req=required_days[city]: 
            days.count(city) == req,
            [f'day_{i}' for i in range(1, 16)]
        )
    
    # Constraint 2: Consecutive days in different cities must have direct flights
    for day in range(1, 15):
        problem.addConstraint(
            lambda city1, city2: city1 == city2 or city2 in direct_flights[city1],
            [f'day_{day}', f'day_{day+1}']
        )
    
    # Constraint 3: Amsterdam must be visited between day 2 and day 3
    problem.addConstraint(
        lambda d2, d3: d2 == 'Amsterdam' or d3 == 'Amsterdam',
        ['day_2', 'day_3']
    )
    
    # Constraint 4: Vilnius workshop between day 7 and day 11
    vilnius_days_constraint = lambda *days: any(days[i] == 'Vilnius' for i in [6, 7, 8, 9, 10])  # indices 6-10 = days 7-11
    problem.addConstraint(vilnius_days_constraint, [f'day_{i}' for i in range(7, 12)])
    
    # Constraint 5: Stockholm wedding between day 13 and day 15
    stockholm_days_constraint = lambda *days: any(days[i] == 'Stockholm' for i in range(3))  # days 13-15
    problem.addConstraint(stockholm_days_constraint, ['day_13', 'day_14', 'day_15'])
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        print(json.dumps({"error": "No valid itinerary found"}))
        return
    
    solution = solutions[0]
    
    # Convert solution to itinerary format
    itinerary = []
    current_city = solution['day_1']
    start_day = 1
    
    for day in range(2, 16):
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
        "day_range": f"Day {start_day}-15",
        "place": current_city
    })
    
    # Verify total days match requirements
    day_counts = {city: 0 for city in cities}
    for day in range(1, 16):
        day_counts[solution[f'day_{day}']] += 1
    
    for city in cities:
        if day_counts[city] != required_days[city]:
            print(json.dumps({"error": f"Day count mismatch for {city}"}))
            return
    
    print(json.dumps({"itinerary": itinerary}, indent=2))

if __name__ == "__main__":
    main()