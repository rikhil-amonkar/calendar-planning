from z3 import *

def solve_itinerary():
    # Cities
    cities = ['Zurich', 'Hamburg', 'Helsinki', 'Bucharest', 'Split']
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Direct flights adjacency list
    direct_flights = {
        'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
        'Hamburg': ['Zurich', 'Bucharest', 'Helsinki', 'Split'],
        'Helsinki': ['Zurich', 'Hamburg', 'Split'],
        'Bucharest': ['Hamburg', 'Zurich'],
        'Split': ['Zurich', 'Helsinki', 'Hamburg']
    }
    
    # Correcting the city names to match the problem statement
    direct_flights = {
        'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
        'Hamburg': ['Zurich', 'Bucharest', 'Helsinki', 'Split'],
        'Helsinki': ['Zurich', 'Hamburg', 'Split'],
        'Bucharest': ['Hamburg', 'Zurich'],
        'Split': ['Zurich', 'Helsinki', 'Hamburg']
    }
    
    # Create Z3 variables
    days = list(range(1, 13))
    day_city = {day: Int(f'day_{day}_city') for day in days}
    
    s = Solver()
    
    # Constraint: each day_city variable must be a valid city index
    for day in days:
        s.add(day_city[day] >= 0, day_city[day] < len(cities))
    
    # Constraints for the number of days in each city
    # Zurich: 3 days (including wedding between day 1 and day 3)
    s.add(Sum([If(day_city[day] == city_to_int['Zurich'], 1, 0) for day in days]) == 3)
    s.add(Or([day_city[day] == city_to_int['Zurich'] for day in range(1, 4)]))
    
    # Hamburg: 2 days
    s.add(Sum([If(day_city[day] == city_to_int['Hamburg'], 1, 0) for day in days]) == 2)
    
    # Helsinki: 2 days
    s.add(Sum([If(day_city[day] == city_to_int['Helsinki'], 1, 0) for day in days]) == 2)
    
    # Bucharest: 2 days
    s.add(Sum([If(day_city[day] == city_to_int['Bucharest'], 1, 0) for day in days]) == 2)
    
    # Split: 7 days (including conferences on day 4 and day 10)
    s.add(Sum([If(day_city[day] == city_to_int['Split'], 1, 0) for day in days]) == 7)
    s.add(day_city[4] == city_to_int['Split'])
    s.add(day_city[10] == city_to_int['Split'])
    
    # Constraints for flight transitions
    for day in range(1, 12):
        current_city = day_city[day]
        next_city = day_city[day + 1]
        # If the city changes, it must be a direct flight
        s.add(Implies(current_city != next_city,
                     Or([And(current_city == city_to_int[city1], next_city == city_to_int[city2])
                        for city1 in cities for city2 in direct_flights[city1])))
    
    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        current_city = None
        start_day = 1
        for day in days:
            city_idx = model.evaluate(day_city[day]).as_long()
            city = int_to_city[city_idx]
            if city != current_city:
                if current_city is not None:
                    itinerary.append({'day_range': f'Day {start_day}-{day-1}', 'place': current_city})
                itinerary.append({'day_range': f'Day {day}', 'place': city})
                start_day = day
                current_city = city
            else:
                continue
        itinerary.append({'day_range': f'Day {start_day}-12', 'place': current_city})
        return {'itinerary': itinerary}
    else:
        return {'itinerary': []}

# Execute the solver
result = solve_itinerary()
print(result)