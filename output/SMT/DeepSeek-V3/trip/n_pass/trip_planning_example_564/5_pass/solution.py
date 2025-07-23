from z3 import *

def solve_itinerary():
    # Cities and their indices
    cities = ['Istanbul', 'Rome', 'Seville', 'Naples', 'Santorini']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: adjacency list (fixed 'Santorini' spelling)
    adjacency = {
        'Rome': ['Santorini', 'Seville', 'Naples', 'Istanbul'],
        'Santorini': ['Rome', 'Naples'],
        'Seville': ['Rome'],
        'Naples': ['Istanbul', 'Santorini', 'Rome'],
        'Istanbul': ['Naples', 'Rome']
    }
    
    # Create Z3 variables for each day (1-based)
    days = 16
    day_vars = [Int(f'day_{i}') for i in range(1, days + 1)]
    
    s = Solver()
    
    # Each day must be one of the cities (0 to 4)
    for day in day_vars:
        s.add(And(day >= 0, day <= 4))
    
    # Specific constraints:
    # Istanbul must include days 6 and 7 (0-based city index is 0)
    s.add(day_vars[5] == city_map['Istanbul'])  # day 6 (1-based is 6, 0-based index is 5)
    s.add(day_vars[6] == city_map['Istanbul'])  # day 7
    
    # Santorini must be days 13-16 (indices 12-15)
    for i in range(12, 16):
        s.add(day_vars[i] == city_map['Santorini'])
    
    # Count days per city (fixed count constraints)
    def count_days(city_idx):
        return Sum([If(day == city_idx, 1, 0) for day in day_vars])
    
    s.add(count_days(city_map['Istanbul']) == 2)
    s.add(count_days(city_map['Rome']) == 3)
    s.add(count_days(city_map['Seville']) == 4)
    s.add(count_days(city_map['Naples']) == 7)
    s.add(count_days(city_map['Santorini']) == 4)
    
    # Flight transitions: consecutive days in different cities must have a direct flight
    for i in range(days - 1):
        current_day = day_vars[i]
        next_day = day_vars[i + 1]
        # If the city changes, ensure there's a direct flight
        s.add(Implies(current_day != next_day, 
                      Or([And(current_day == city_map[city1], next_day == city_map[city2]) 
                          for city1 in adjacency 
                          for city2 in adjacency[city1]])))
    
    # Additional constraints to help the solver:
    # 1. Must start somewhere (let's say Rome as it's well-connected)
    s.add(day_vars[0] == city_map['Rome'])
    # 2. Must end in Santorini (since days 13-16 are there)
    s.add(day_vars[15] == city_map['Santorini'])
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(1, days + 1):
            day_var = day_vars[i-1]
            city_idx = m[day_var].as_long()
            city = cities[city_idx]
            itinerary.append({'day': i, 'place': city})
        return {'itinerary': itinerary}
    else:
        print("No valid itinerary found")
        return None

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))