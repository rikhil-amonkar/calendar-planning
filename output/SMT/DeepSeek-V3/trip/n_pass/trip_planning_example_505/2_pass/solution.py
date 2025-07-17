from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Prague', 'Stuttgart', 'Split', 'Krakow', 'Florence']
    city_map = {city: idx for idx, city in enumerate(cities)}
    n_cities = len(cities)
    
    # Direct flights as adjacency list
    direct_flights = {
        'Stuttgart': ['Split', 'Krakow'],
        'Prague': ['Florence', 'Split', 'Krakow'],
        'Krakow': ['Stuttgart', 'Split', 'Prague'],
        'Split': ['Stuttgart', 'Krakow', 'Prague'],
        'Florence': ['Prague']
    }
    
    # Days: 1 to 8
    days = 8
    
    s = Solver()
    
    # Create Z3 variables: for each day, the current city (0-based index)
    city_vars = [Int(f'city_{day}') for day in range(days)]
    for day in range(days):
        s.add(city_vars[day] >= 0, city_vars[day] < n_cities)
    
    # Transition constraints: if city changes between day X and X+1, they must be connected by a direct flight.
    for day in range(days - 1):
        current_city_var = city_vars[day]
        next_city_var = city_vars[day + 1]
        # If cities are different, they must have a direct flight.
        s.add(Implies(current_city_var != next_city_var,
                      Or([And(current_city_var == city_map[c], next_city_var == city_map[n])
                          for c in direct_flights for n in direct_flights[c]])))
    
    # Function to check if a city is present on a day.
    def is_present(day, city_idx):
        # The city is present on this day if:
        # - It's the current city for the day.
        # - Or it's the next city for the previous day (if previous day is a transition day).
        conditions = [city_vars[day] == city_idx]
        if day > 0:
            conditions.append(And(city_vars[day - 1] != city_vars[day], city_vars[day] == city_idx))
        return Or(conditions)
    
    # Total days per city constraints.
    for city in cities:
        city_idx = city_map[city]
        total_days = Sum([If(is_present(day, city_idx), 1, 0) for day in range(days)])
        if city == 'Prague':
            s.add(total_days == 4)
        elif city == 'Stuttgart':
            s.add(total_days == 2)
            # Wedding between day 2 and 3 (1-based), so day 1 or 2 in 0-based.
            s.add(Or(is_present(1, city_idx), is_present(2, city_idx)))
        elif city == 'Split':
            s.add(total_days == 2)
            # Meeting friends between day 3 and 4 (1-based), so day 2 or 3 in 0-based.
            s.add(Or(is_present(2, city_idx), is_present(3, city_idx)))
        elif city == 'Krakow':
            s.add(total_days == 2)
        elif city == 'Florence':
            s.add(total_days == 2)
    
    # Solve the model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(days):
            current_day = day + 1  # 1-based
            current_city_idx = model.eval(city_vars[day]).as_long()
            current_city = cities[current_city_idx]
            places = [current_city]
            # Check if this is a transition day (next day is different)
            if day < days - 1:
                next_city_idx = model.eval(city_vars[day + 1]).as_long()
                if next_city_idx != current_city_idx:
                    next_city = cities[next_city_idx]
                    places.append(next_city)
            itinerary.append({'day': current_day, 'place': places})
        
        result = {'itinerary': itinerary}
        return result
    else:
        return None

s = Solver()
result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")