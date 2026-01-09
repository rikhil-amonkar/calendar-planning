import json
from constraint import Problem, AllDifferentConstraint

def solve_trip_plan():
    # Define the cities and their required days
    cities = {
        'Oslo': 2,
        'Stuttgart': 3,
        'Venice': 4,
        'Split': 4,
        'Barcelona': 3,
        'Brussels': 3,
        'Copenhagen': 3
    }
    
    # Define direct flight connections
    direct_flights = {
        'Venice': ['Stuttgart', 'Barcelona', 'Brussels', 'Copenhagen', 'Oslo'],
        'Stuttgart': ['Venice', 'Barcelona', 'Copenhagen', 'Split'],
        'Oslo': ['Brussels', 'Split', 'Venice', 'Copenhagen', 'Barcelona'],
        'Split': ['Copenhagen', 'Oslo', 'Barcelona', 'Stuttgart'],
        'Barcelona': ['Copenhagen', 'Venice', 'Stuttgart', 'Split', 'Oslo', 'Brussels'],
        'Brussels': ['Oslo', 'Venice', 'Copenhagen'],
        'Copenhagen': ['Split', 'Barcelona', 'Brussels', 'Oslo', 'Stuttgart', 'Venice']
    }
    
    # Create constraint problem
    problem = Problem()
    
    # Variables: city order (0-6 for 7 cities)
    num_cities = len(cities)
    city_names = list(cities.keys())
    
    # Add variables for city positions
    problem.addVariables(range(num_cities), range(num_cities))
    problem.addConstraint(AllDifferentConstraint(), range(num_cities))
    
    # Add flight connectivity constraints
    def flight_constraint(*positions):
        city_order = [None] * num_cities
        for i, pos in enumerate(positions):
            city_order[pos] = city_names[i]
        
        # Check consecutive cities are connected by direct flights
        for i in range(num_cities - 1):
            city1 = city_order[i]
            city2 = city_order[i + 1]
            if city2 not in direct_flights[city1]:
                return False
        return True
    
    problem.addConstraint(flight_constraint, range(num_cities))
    
    # Add duration constraints (total days = 16)
    def duration_constraint(*positions):
        city_order = [None] * num_cities
        for i, pos in enumerate(positions):
            city_order[pos] = city_names[i]
        
        total_days = sum(cities.values())
        return total_days == 16
    
    problem.addConstraint(duration_constraint, range(num_cities))
    
    # Find a solution
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use first solution
    solution = solutions[0]
    
    # Reconstruct city order from solution
    city_order = [None] * num_cities
    for i in range(num_cities):
        city_order[solution[i]] = city_names[i]
    
    # Calculate day ranges
    itinerary = []
    current_day = 1
    
    for i, city in enumerate(city_order):
        duration = cities[city]
        end_day = current_day + duration - 1
        
        # Check special constraints
        if city == 'Barcelona':
            # Barcelona must include days 1-3
            if not (current_day <= 3 <= end_day):
                # Try to rearrange to satisfy Barcelona constraint
                for j in range(i + 1, num_cities):
                    if city_order[j] == 'Barcelona':
                        # Swap cities
                        city_order[i], city_order[j] = city_order[j], city_order[i]
                        break
        
        elif city == 'Oslo':
            # Oslo must be between day 3 and day 4
            if not (current_day <= 4 <= end_day or current_day <= 3 <= end_day):
                for j in range(i + 1, num_cities):
                    if city_order[j] == 'Oslo':
                        city_order[i], city_order[j] = city_order[j], city_order[i]
                        break
        
        elif city == 'Brussels':
            # Brussels must include days 9-11
            if not (current_day <= 11 <= end_day or current_day <= 9 <= end_day):
                for j in range(i + 1, num_cities):
                    if city_order[j] == 'Brussels':
                        city_order[i], city_order[j] = city_order[j], city_order[i]
                        break
    
    # Recalculate day ranges with adjusted order
    itinerary = []
    current_day = 1
    
    for city in city_order:
        duration = cities[city]
        end_day = current_day + duration - 1
        
        day_range = f"Day {current_day}-{end_day}"
        itinerary.append({"day_range": day_range, "place": city})
        current_day = end_day + 1
    
    # Verify all constraints are satisfied
    barcelona_ok = False
    oslo_ok = False
    brussels_ok = False
    
    for item in itinerary:
        city = item['place']
        day_range = item['day_range']
        start_day = int(day_range.split('-')[0].split(' ')[1])
        end_day = int(day_range.split('-')[1])
        
        if city == 'Barcelona':
            if start_day <= 3 <= end_day:
                barcelona_ok = True
        elif city == 'Oslo':
            if (start_day <= 3 <= end_day) or (start_day <= 4 <= end_day):
                oslo_ok = True
        elif city == 'Brussels':
            if (start_day <= 9 <= end_day) or (start_day <= 11 <= end_day):
                brussels_ok = True
    
    # If constraints not satisfied, try to find a valid arrangement
    if not (barcelona_ok and oslo_ok and brussels_ok):
        # Try different permutations manually
        valid_orders = [
            ['Barcelona', 'Oslo', 'Brussels', 'Copenhagen', 'Split', 'Venice', 'Stuttgart'],
            ['Barcelona', 'Oslo', 'Copenhagen', 'Brussels', 'Split', 'Venice', 'Stuttgart'],
            ['Barcelona', 'Venice', 'Oslo', 'Brussels', 'Copenhagen', 'Split', 'Stuttgart']
        ]
        
        for order in valid_orders:
            # Check flight connectivity
            valid_order = True
            for i in range(len(order) - 1):
                if order[i + 1] not in direct_flights[order[i]]:
                    valid_order = False
                    break
            
            if valid_order:
                itinerary = []
                current_day = 1
                
                for city in order:
                    duration = cities[city]
                    end_day = current_day + duration - 1
                    
                    day_range = f"Day {current_day}-{end_day}"
                    itinerary.append({"day_range": day_range, "place": city})
                    current_day = end_day + 1
                
                # Verify constraints
                barcelona_ok = False
                oslo_ok = False
                brussels_ok = False
                
                for item in itinerary:
                    city = item['place']
                    day_range = item['day_range']
                    start_day = int(day_range.split('-')[0].split(' ')[1])
                    end_day = int(day_range.split('-')[1])
                    
                    if city == 'Barcelona':
                        if start_day <= 3 <= end_day:
                            barcelona_ok = True
                    elif city == 'Oslo':
                        if (start_day <= 3 <= end_day) or (start_day <= 4 <= end_day):
                            oslo_ok = True
                    elif city == 'Brussels':
                        if (start_day <= 9 <= end_day) or (start_day <= 11 <= end_day):
                            brussels_ok = True
                
                if barcelona_ok and oslo_ok and brussels_ok:
                    break
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_trip_plan()
    print(json.dumps(result, indent=2))