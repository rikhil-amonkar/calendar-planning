from z3 import *

def solve_itinerary():
    # Cities and their direct flight connections
    cities = ['Porto', 'Amsterdam', 'Helsinki', 'Naples', 'Brussels', 'Split', 
              'Reykjavik', 'Lyon', 'Warsaw', 'Valencia']
    
    direct_flights = {
        'Amsterdam': ['Warsaw', 'Lyon', 'Naples', 'Reykjavik', 'Split', 'Porto', 'Helsinki', 'Valencia'],
        'Helsinki': ['Brussels', 'Warsaw', 'Split', 'Naples', 'Reykjavik', 'Amsterdam'],
        'Reykjavik': ['Brussels', 'Warsaw', 'Amsterdam', 'Helsinki'],
        'Naples': ['Valencia', 'Amsterdam', 'Split', 'Brussels', 'Warsaw'],
        'Porto': ['Brussels', 'Amsterdam', 'Lyon', 'Warsaw', 'Valencia'],
        'Split': ['Amsterdam', 'Lyon', 'Warsaw', 'Naples', 'Helsinki'],
        'Lyon': ['Amsterdam', 'Split', 'Brussels', 'Valencia', 'Porto'],
        'Warsaw': ['Amsterdam', 'Helsinki', 'Split', 'Reykjavik', 'Brussels', 'Naples', 'Valencia', 'Porto'],
        'Brussels': ['Helsinki', 'Reykjavik', 'Porto', 'Lyon', 'Valencia', 'Naples', 'Warsaw'],
        'Valencia': ['Naples', 'Brussels', 'Lyon', 'Warsaw', 'Amsterdam', 'Porto']
    }
    
    # Create solver
    s = Solver()
    
    # Days are 1..27
    days = 27
    day_city = [Int(f'day_{i}_city') for i in range(1, days+1)]
    
    # City to index mapping
    city_to_idx = {city: idx for idx, city in enumerate(cities)}
    idx_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Constraints for each day: must be a valid city index (0..9)
    for day in day_city:
        s.add(day >= 0, day < len(cities))
    
    # Fixed events
    # Porto days 1-5 (workshop)
    for day in range(1, 6):
        s.add(day_city[day-1] == city_to_idx['Porto'])
    
    # Amsterdam days 6-8 (relatives)
    for day in range(6, 9):
        s.add(day_city[day-1] == city_to_idx['Amsterdam'])
    
    # Helsinki days 9-11 (wedding)
    for day in range(9, 12):
        s.add(day_city[day-1] == city_to_idx['Helsinki'])
    
    # Naples days 17-20 (conference)
    for day in range(17, 21):
        s.add(day_city[day-1] == city_to_idx['Naples'])
    
    # Brussels days 21-22 (annual show)
    for day in range(21, 23):
        s.add(day_city[day-1] == city_to_idx['Brussels'])
    
    # Total days per city requirements
    city_days = {
        'Porto': 5,
        'Amsterdam': 4,
        'Helsinki': 4,
        'Naples': 4,
        'Brussels': 3,
        'Split': 3,
        'Reykjavik': 5,
        'Lyon': 3,
        'Warsaw': 3,
        'Valencia': 2
    }
    
    # Count days in each city
    for city in cities:
        total = Sum([If(day_city[i] == city_to_idx[city], 1, 0) for i in range(days)])
        s.add(total == city_days[city])
    
    # Flight constraints
    for i in range(days - 1):
        current = day_city[i]
        next_day = day_city[i+1]
        # If changing cities, must have direct flight
        s.add(Implies(current != next_day,
                     Or([And(current == city_to_idx[a], next_day == city_to_idx[b])
                        for a in direct_flights for b in direct_flights[a]])))
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            city_idx = model.evaluate(day_city[i]).as_long()
            itinerary.append({"day": i+1, "place": idx_to_city[city_idx]})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Solve and print the itinerary
result = solve_itinerary()
print(result)