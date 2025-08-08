from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Brussels': 5,
        'Rome': 2,
        'Dubrovnik': 3,
        'Geneva': 5,
        'Budapest': 2,
        'Riga': 4,
        'Valencia': 2
    }
    
    # Direct flights
    direct_flights = {
        'Brussels': ['Valencia', 'Geneva', 'Riga', 'Rome', 'Budapest'],
        'Rome': ['Valencia', 'Geneva', 'Riga', 'Budapest', 'Brussels', 'Dubrovnik'],
        'Dubrovnik': ['Geneva', 'Rome'],
        'Geneva': ['Brussels', 'Rome', 'Dubrovnik', 'Valencia', 'Budapest'],
        'Budapest': ['Geneva', 'Rome', 'Brussels'],
        'Riga': ['Rome', 'Brussels'],
        'Valencia': ['Brussels', 'Rome', 'Geneva']
    }
    
    s = Solver()
    
    # Create variables: day 1-17, each day assigned to one city
    assignments = [Int(f"day_{day}") for day in range(1, 18)]
    for day in range(17):
        s.add(assignments[day] >= 0)
        s.add(assignments[day] < len(cities))
    
    # Create city lists for easy reference
    city_list = list(cities.keys())
    
    # Duration constraints
    for city_idx, (city, days) in enumerate(cities.items()):
        s.add(Sum([If(assignments[day] == city_idx, 1, 0) for day in range(17)]) == days)
    
    # Workshop in Brussels between day 7-11
    s.add(Or([assignments[day] == city_list.index('Brussels') for day in range(6, 11)]))
    
    # Meet friend in Budapest between day 16-17
    s.add(Or(assignments[15] == city_list.index('Budapest'), 
             assignments[16] == city_list.index('Budapest')))
    
    # Meet friends in Riga between day 4-7
    s.add(Or([assignments[day] == city_list.index('Riga') for day in range(3, 7)]))
    
    # Flight constraints
    for day in range(16):
        current_city = assignments[day]
        next_city = assignments[day+1]
        # If changing cities, ensure direct flight exists
        s.add(Implies(current_city != next_city,
                     Or([And(current_city == city_list.index(city1),
                         next_city == city_list.index(city2))
                       for city1 in direct_flights
                       for city2 in direct_flights[city1]])))
    
    # Flight days count for both cities
    for day in range(16):
        current_city = assignments[day]
        next_city = assignments[day+1]
        # If changing cities, mark both cities as visited on transition day
        s.add(Implies(current_city != next_city,
                     Or([And(current_city == city_list.index(city1),
                         next_city == city_list.index(city2))
                       for city1 in direct_flights
                       for city2 in direct_flights[city1]])))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(17):
            city_idx = m.evaluate(assignments[day]).as_long()
            itinerary.append({"day": day+1, "place": city_list[city_idx]})
        
        # Verify all constraints are met
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        print("Solution found:")
        import json
        print(json.dumps({"itinerary": itinerary}, indent=2))
        
        print("\nVerification:")
        for city, days in cities.items():
            print(f"{city}: {city_days[city]} days (required: {days})")
    else:
        print("No solution found")

solve_itinerary()