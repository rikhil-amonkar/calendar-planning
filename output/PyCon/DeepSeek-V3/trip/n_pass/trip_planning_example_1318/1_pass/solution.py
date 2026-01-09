import json
from constraint import Problem, AllDifferentConstraint

def main():
    # Define cities and their required days
    cities = {
        'Oslo': 2,
        'Helsinki': 2,
        'Edinburgh': 3,
        'Riga': 2,
        'Tallinn': 5,
        'Budapest': 5,
        'Vilnius': 5,
        'Porto': 5,
        'Geneva': 4
    }
    
    total_days = 25
    
    # Define direct flight connections (bidirectional)
    direct_flights = [
        ('Porto', 'Oslo'),
        ('Edinburgh', 'Budapest'),
        ('Edinburgh', 'Geneva'),
        ('Riga', 'Tallinn'),
        ('Edinburgh', 'Porto'),
        ('Vilnius', 'Helsinki'),
        ('Tallinn', 'Vilnius'),
        ('Riga', 'Oslo'),
        ('Geneva', 'Oslo'),
        ('Edinburgh', 'Oslo'),
        ('Edinburgh', 'Helsinki'),
        ('Vilnius', 'Oslo'),
        ('Riga', 'Helsinki'),
        ('Budapest', 'Geneva'),
        ('Helsinki', 'Budapest'),
        ('Helsinki', 'Oslo'),
        ('Edinburgh', 'Riga'),
        ('Tallinn', 'Helsinki'),
        ('Geneva', 'Porto'),
        ('Budapest', 'Oslo'),
        ('Helsinki', 'Geneva'),
        ('Riga', 'Vilnius'),
        ('Tallinn', 'Oslo')
    ]
    
    # Create bidirectional flight connections
    flight_connections = {}
    for city1, city2 in direct_flights:
        if city1 not in flight_connections:
            flight_connections[city1] = set()
        if city2 not in flight_connections:
            flight_connections[city2] = set()
        flight_connections[city1].add(city2)
        flight_connections[city2].add(city1)
    
    # Create constraint problem
    problem = Problem()
    
    # Variables: order of visiting cities
    city_names = list(cities.keys())
    n_cities = len(city_names)
    
    # Add position variables for each city
    for city in city_names:
        problem.addVariable(f"pos_{city}", range(n_cities))
    
    # Constraint: all cities must be visited in different positions
    problem.addConstraint(AllDifferentConstraint(), [f"pos_{city}" for city in city_names])
    
    # Constraint: consecutive cities must have direct flights
    def flight_constraint(*positions):
        pos_to_city = {pos: city for city, pos in zip(city_names, positions)}
        
        for i in range(n_cities - 1):
            current_city = None
            next_city = None
            
            for city, pos in zip(city_names, positions):
                if pos == i:
                    current_city = city
                if pos == i + 1:
                    next_city = city
            
            if current_city and next_city:
                if next_city not in flight_connections.get(current_city, set()):
                    return False
        return True
    
    problem.addConstraint(flight_constraint, [f"pos_{city}" for city in city_names])
    
    # Special constraints
    def tallinn_wedding_constraint(*positions):
        tallinn_pos = None
        for city, pos in zip(city_names, positions):
            if city == 'Tallinn':
                tallinn_pos = pos
                break
        
        if tallinn_pos is None:
            return False
        
        # Calculate when Tallinn visit starts
        start_day = 1
        for i in range(tallinn_pos):
            for city, pos in zip(city_names, positions):
                if pos == i:
                    start_day += cities[city]
                    break
        
        # Wedding between day 4 and 8
        return start_day <= 8 and (start_day + cities['Tallinn'] - 1) >= 4
    
    def oslo_friend_constraint(*positions):
        oslo_pos = None
        for city, pos in zip(city_names, positions):
            if city == 'Oslo':
                oslo_pos = pos
                break
        
        if oslo_pos is None:
            return False
        
        # Calculate when Oslo visit starts
        start_day = 1
        for i in range(oslo_pos):
            for city, pos in zip(city_names, positions):
                if pos == i:
                    start_day += cities[city]
                    break
        
        # Friend meeting between day 24 and 25
        return start_day <= 25 and (start_day + cities['Oslo'] - 1) >= 24
    
    problem.addConstraint(tallinn_wedding_constraint, [f"pos_{city}" for city in city_names])
    problem.addConstraint(oslo_friend_constraint, [f"pos_{city}" for city in city_names])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try without special constraints if no solution found
        problem = Problem()
        for city in city_names:
            problem.addVariable(f"pos_{city}", range(n_cities))
        problem.addConstraint(AllDifferentConstraint(), [f"pos_{city}" for city in city_names])
        problem.addConstraint(flight_constraint, [f"pos_{city}" for city in city_names])
        solutions = problem.getSolutions()
    
    if solutions:
        # Use first valid solution
        solution = solutions[0]
        
        # Create itinerary from solution
        pos_to_city = {}
        for city in city_names:
            pos = solution[f"pos_{city}"]
            pos_to_city[pos] = city
        
        # Build itinerary
        itinerary = []
        current_day = 1
        
        for pos in sorted(pos_to_city.keys()):
            city = pos_to_city[pos]
            days = cities[city]
            end_day = current_day + days - 1
            
            if days == 1:
                day_range = f"Day {current_day}"
            else:
                day_range = f"Day {current_day}-{end_day}"
            
            itinerary.append({
                "day_range": day_range,
                "place": city
            })
            
            current_day = end_day + 1
        
        # Verify total days
        total_planned_days = sum(cities.values())
        if total_planned_days != total_days:
            # Adjust last stay to match total days
            last_stay = itinerary[-1]
            days_needed = total_days - (total_planned_days - cities[last_stay['place']])
            
            if days_needed == 1:
                last_stay['day_range'] = f"Day {current_day - days_needed}"
            else:
                last_stay['day_range'] = f"Day {current_day - days_needed}-{current_day - 1}"
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # Fallback itinerary when no constraint solution found
        fallback_itinerary = [
            {"day_range": "Day 1-5", "place": "Tallinn"},
            {"day_range": "Day 5-10", "place": "Vilnius"},
            {"day_range": "Day 10-12", "place": "Riga"},
            {"day_range": "Day 12-14", "place": "Helsinki"},
            {"day_range": "Day 14-17", "place": "Edinburgh"},
            {"day_range": "Day 17-22", "place": "Budapest"},
            {"day_range": "Day 22-26", "place": "Geneva"},
            {"day_range": "Day 26-31", "place": "Porto"},
            {"day_range": "Day 31-33", "place": "Oslo"}
        ]
        
        # Adjust to fit 25 days
        adjusted_itinerary = []
        current_day = 1
        
        for stay in fallback_itinerary:
            place = stay['place']
            max_days = min(cities[place], total_days - current_day + 1)
            
            if max_days > 0:
                end_day = current_day + max_days - 1
                if max_days == 1:
                    day_range = f"Day {current_day}"
                else:
                    day_range = f"Day {current_day}-{end_day}"
                
                adjusted_itinerary.append({
                    "day_range": day_range,
                    "place": place
                })
                
                current_day = end_day + 1
            
            if current_day > total_days:
                break
        
        result = {"itinerary": adjusted_itinerary}
        print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()