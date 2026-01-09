import constraint
import json

def main():
    # Define the problem
    problem = constraint.Problem()
    
    # Cities and their required days
    cities = {
        'Venice': 3,
        'Reykjavik': 2,
        'Munich': 3,
        'Santorini': 3,
        'Manchester': 3,
        'Porto': 3,
        'Bucharest': 5,
        'Tallinn': 4,
        'Valencia': 2,
        'Vienna': 5
    }
    
    # Direct flight connections (bidirectional)
    connections = {
        'Bucharest': ['Manchester', 'Valencia', 'Vienna'],
        'Munich': ['Venice', 'Porto', 'Reykjavik', 'Manchester', 'Vienna', 'Bucharest', 'Valencia', 'Tallinn'],
        'Santorini': ['Manchester', 'Venice', 'Vienna', 'Bucharest'],
        'Vienna': ['Reykjavik', 'Valencia', 'Manchester', 'Porto', 'Venice', 'Bucharest', 'Santorini', 'Munich'],
        'Venice': ['Munich', 'Santorini', 'Manchester', 'Vienna'],
        'Manchester': ['Bucharest', 'Santorini', 'Vienna', 'Porto', 'Venice', 'Munich'],
        'Porto': ['Munich', 'Vienna', 'Valencia', 'Manchester'],
        'Valencia': ['Vienna', 'Bucharest', 'Porto', 'Munich'],
        'Reykjavik': ['Vienna', 'Munich'],
        'Tallinn': ['Munich']
    }
    
    # Fixed constraints
    fixed_constraints = [
        ('Munich', 4, 6),  # Munich from day 4 to day 6
        ('Santorini', 8, 10),  # Santorini from day 8 to day 10
        ('Valencia', 14, 15)  # Valencia from day 14 to day 15
    ]
    
    total_days = 24
    city_list = list(cities.keys())
    
    # Create variables for start day of each city visit
    for city in city_list:
        problem.addVariable(f'start_{city}', range(1, total_days + 1))
    
    # Constraint: all visits must be within the 24-day period and respect duration
    for city in city_list:
        duration = cities[city]
        problem.addConstraint(
            lambda start, dur=duration: start >= 1 and start + dur - 1 <= total_days,
            (f'start_{city}',)
        )
    
    # Constraint: no overlapping visits to different cities
    for i, city1 in enumerate(city_list):
        for j, city2 in enumerate(city_list):
            if i < j:
                problem.addConstraint(
                    lambda s1, s2, dur1=cities[city1], dur2=cities[city2]: 
                    s1 + dur1 - 1 < s2 or s2 + dur2 - 1 < s1,
                    (f'start_{city1}', f'start_{city2}')
                )
    
    # Constraint: fixed date constraints
    for city, start_day, end_day in fixed_constraints:
        problem.addConstraint(
            lambda s, fixed_s=start_day: s == fixed_s,
            (f'start_{city}',)
        )
    
    # Find initial solution without flight constraints
    solutions = problem.getSolutions()
    
    if not solutions:
        print('{"error": "No valid itinerary found due to date constraints"}')
        return
    
    # Now find a solution that satisfies flight connections
    valid_solution = None
    
    for solution in solutions:
        # Create visit schedule
        visits = []
        for city in city_list:
            start = solution[f'start_{city}']
            end = start + cities[city] - 1
            visits.append((start, city))
        
        # Sort visits by start day
        visits.sort(key=lambda x: x[0])
        
        # Check if consecutive visits are connected by flights
        valid = True
        for i in range(len(visits) - 1):
            current_city = visits[i][1]
            next_city = visits[i + 1][1]
            
            # Check if there's a direct flight between current and next city
            if next_city not in connections.get(current_city, []):
                valid = False
                break
        
        if valid:
            valid_solution = solution
            break
    
    if valid_solution:
        # Create itinerary
        itinerary = []
        city_visits = []
        
        for city in city_list:
            start = valid_solution[f'start_{city}']
            end = start + cities[city] - 1
            city_visits.append((start, end, city))
        
        # Sort by start day
        city_visits.sort(key=lambda x: x[0])
        
        for start, end, city in city_visits:
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range, "place": city})
        
        # Verify all constraints are satisfied
        print("Valid itinerary found that satisfies all constraints!")
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"error": "No valid itinerary found with required flight connections"}')

if __name__ == "__main__":
    main()