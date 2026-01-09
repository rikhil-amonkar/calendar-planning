import json
from constraint import Problem, AllDifferentConstraint

def solve_trip_plan():
    # Define the problem
    problem = Problem()
    
    # Cities and their required days
    cities = {
        'Frankfurt': 4,
        'Manchester': 4,
        'Valencia': 4,
        'Naples': 4,
        'Oslo': 3,
        'Vilnius': 2
    }
    
    total_days = 16
    
    # Direct flight connections
    direct_flights = {
        'Valencia': ['Frankfurt', 'Naples'],
        'Manchester': ['Frankfurt', 'Naples', 'Oslo'],
        'Naples': ['Valencia', 'Manchester', 'Frankfurt', 'Oslo'],
        'Oslo': ['Naples', 'Frankfurt', 'Vilnius', 'Manchester'],
        'Vilnius': ['Frankfurt', 'Oslo'],
        'Frankfurt': ['Valencia', 'Manchester', 'Naples', 'Oslo', 'Vilnius']
    }
    
    # Fixed constraints
    # Frankfurt from day 13 to 16 (4 days)
    # Wedding in Vilnius between day 12 and 13 (2 days total)
    
    # Create variables for start days of each city visit
    # We'll model this as finding the order of cities to visit
    city_names = list(cities.keys())
    
    # We need to assign positions to cities in the itinerary
    problem.addVariables(range(len(city_names)), city_names)
    problem.addConstraint(AllDifferentConstraint(), range(len(city_names)))
    
    # We'll also need variables for start days
    start_days = {}
    for city in city_names:
        start_days[city] = f"start_{city}"
    
    problem.addVariables(list(start_days.values()), range(1, total_days + 1))
    
    # Fixed constraints
    # Frankfurt must include days 13-16
    problem.addConstraint(lambda start_Frankfurt: start_Frankfurt <= 13 and start_Frankfurt + cities['Frankfurt'] - 1 >= 16, 
                         ['start_Frankfurt'])
    
    # Vilnius wedding between day 12-13, so it must include these days
    problem.addConstraint(lambda start_Vilnius: start_Vilnius <= 12 and start_Vilnius + cities['Vilnius'] - 1 >= 13, 
                         ['start_Vilnius'])
    
    # All visits must be within the 16-day period
    for city in city_names:
        problem.addConstraint(lambda start, city=city: start + cities[city] - 1 <= total_days, 
                             [f'start_{city}'])
    
    # No overlapping visits
    for i, city1 in enumerate(city_names):
        for j, city2 in enumerate(city_names):
            if i < j:
                problem.addConstraint(
                    lambda start1, start2, c1=city1, c2=city2: 
                    start1 + cities[c1] <= start2 or start2 + cities[c2] <= start1,
                    [f'start_{city1}', f'start_{city2}']
                )
    
    # Flight connectivity constraints
    # Each transition must be via direct flight
    city_order_vars = list(range(len(city_names)))
    
    def flight_connectivity_constraint(*ordered_cities):
        for i in range(len(ordered_cities) - 1):
            city1 = ordered_cities[i]
            city2 = ordered_cities[i + 1]
            if city2 not in direct_flights[city1]:
                return False
        return True
    
    problem.addConstraint(flight_connectivity_constraint, city_order_vars)
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first solution
    solution = solutions[0]
    
    # Extract the order of cities from the solution
    city_order = []
    for i in range(len(city_names)):
        city_order.append(solution[i])
    
    # Calculate start days for each city
    itinerary_data = []
    current_day = 1
    
    for i, city in enumerate(city_order):
        start_day = solution[f'start_{city}']
        end_day = start_day + cities[city] - 1
        
        # Adjust for flight days - when we fly, we're in both cities on that day
        if i > 0:
            # The flight day is counted in both cities
            pass
        
        itinerary_data.append({
            'city': city,
            'start_day': start_day,
            'end_day': end_day,
            'duration': cities[city]
        })
    
    # Sort by start day
    itinerary_data.sort(key=lambda x: x['start_day'])
    
    # Create the final itinerary in the required format
    itinerary = []
    for visit in itinerary_data:
        if visit['start_day'] == visit['end_day']:
            day_range = f"Day {visit['start_day']}"
        else:
            day_range = f"Day {visit['start_day']}-{visit['end_day']}"
        
        itinerary.append({
            'day_range': day_range,
            'place': visit['city']
        })
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_trip_plan()
    print(json.dumps(result, indent=2))