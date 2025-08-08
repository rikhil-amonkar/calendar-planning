from z3 import *

def solve_itinerary():
    # Cities involved
    cities = ['Paris', 'Warsaw', 'Krakow', 'Tallinn', 'Riga', 'Copenhagen', 'Helsinki', 'Oslo', 'Santorini', 'Lyon']
    
    # Direct flights as a dictionary for quick lookup
    direct_flights = {
        'Warsaw': ['Riga', 'Tallinn', 'Copenhagen', 'Helsinki', 'Paris', 'Oslo', 'Krakow'],
        'Riga': ['Warsaw', 'Tallinn', 'Helsinki', 'Oslo', 'Paris', 'Copenhagen'],
        'Tallinn': ['Warsaw', 'Riga', 'Oslo', 'Helsinki', 'Copenhagen', 'Paris'],
        'Copenhagen': ['Helsinki', 'Warsaw', 'Santorini', 'Krakow', 'Riga', 'Oslo', 'Tallinn', 'Paris'],
        'Helsinki': ['Copenhagen', 'Warsaw', 'Riga', 'Tallinn', 'Oslo', 'Krakow', 'Paris'],
        'Oslo': ['Lyon', 'Paris', 'Riga', 'Warsaw', 'Helsinki', 'Tallinn', 'Krakow', 'Santorini', 'Copenhagen'],
        'Santorini': ['Copenhagen', 'Oslo'],
        'Lyon': ['Paris', 'Oslo'],
        'Paris': ['Lyon', 'Oslo', 'Riga', 'Tallinn', 'Warsaw', 'Helsinki', 'Krakow', 'Copenhagen'],
        'Krakow': ['Helsinki', 'Warsaw', 'Copenhagen', 'Paris', 'Oslo']
    }
    
    # Correcting city name inconsistencies in direct_flights
    direct_flights['Paris'] = ['Lyon', 'Oslo', 'Riga', 'Tallinn', 'Warsaw', 'Helsinki', 'Krakow', 'Copenhagen']
    direct_flights['Riga'] = ['Warsaw', 'Tallinn', 'Helsinki', 'Oslo', 'Paris', 'Copenhagen']
    direct_flights['Tallinn'] = ['Warsaw', 'Riga', 'Oslo', 'Helsinki', 'Copenhagen', 'Paris']
    
    # Create a Z3 solver instance
    s = Solver()
    
    # Create a list of days (1..25)
    days = 25
    day_numbers = [i+1 for i in range(days)]
    
    # Create Z3 variables for each day: the city visited on that day
    city_vars = [Int(f'day_{i}_city') for i in day_numbers]
    
    # Assign each city a unique integer
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Add constraints that each city_var must be one of the city integers
    for day in city_vars:
        s.add(Or([day == city_to_int[city] for city in cities]))
    
    # Constraints for city visits durations
    # Paris: 5 days
    s.add(Sum([If(city_vars[i] == city_to_int['Paris'], 1, 0) for i in range(days)]) == 5)
    # Warsaw: 2 days
    s.add(Sum([If(city_vars[i] == city_to_int['Warsaw'], 1, 0) for i in range(days)]) == 2)
    # Krakow: 2 days
    s.add(Sum([If(city_vars[i] == city_to_int['Krakow'], 1, 0) for i in range(days)]) == 2)
    # Tallinn: 2 days
    s.add(Sum([If(city_vars[i] == city_to_int['Tallinn'], 1, 0) for i in range(days)]) == 2)
    # Riga: 2 days
    s.add(Sum([If(city_vars[i] == city_to_int['Riga'], 1, 0) for i in range(days)]) == 2)
    # Copenhagen: 5 days
    s.add(Sum([If(city_vars[i] == city_to_int['Copenhagen'], 1, 0) for i in range(days)]) == 5)
    # Helsinki: 5 days
    s.add(Sum([If(city_vars[i] == city_to_int['Helsinki'], 1, 0) for i in range(days)]) == 5)
    # Oslo: 5 days
    s.add(Sum([If(city_vars[i] == city_to_int['Oslo'], 1, 0) for i in range(days)]) == 5)
    # Santorini: 2 days
    s.add(Sum([If(city_vars[i] == city_to_int['Santorini'], 1, 0) for i in range(days)]) == 2)
    # Lyon: 4 days
    s.add(Sum([If(city_vars[i] == city_to_int['Lyon'], 1, 0) for i in range(days)]) == 4)
    
    # Event constraints
    # Paris between day 4 and 8 (at least one day in this range)
    s.add(Sum([If(And(city_vars[i] == city_to_int['Paris'], i+1 >= 4, i+1 <= 8), 1, 0) for i in range(days)]) >= 1)
    # Krakow workshop between day 17 and 18 (must be in Krakow on at least one of these days)
    s.add(Or([And(city_vars[i] == city_to_int['Krakow'], i+1 >= 17, i+1 <= 18) for i in range(days)]))
    # Riga wedding between day 23 and 24 (must be in Riga on at least one of these days)
    s.add(Or([And(city_vars[i] == city_to_int['Riga'], i+1 >= 23, i+1 <= 24) for i in range(days)]))
    # Helsinki friend between day 18 and 22 (must be in Helsinki on at least one of these days)
    s.add(Or([And(city_vars[i] == city_to_int['Helsinki'], i+1 >= 18, i+1 <= 22) for i in range(days)]))
    # Santorini relatives between day 12 and 13 (must be in Santorini on at least one of these days)
    s.add(Or([And(city_vars[i] == city_to_int['Santorini'], i+1 >= 12, i+1 <= 13) for i in range(days)]))
    
    # Flight constraints: consecutive days must be same city or have a direct flight
    for i in range(days - 1):
        current_city = city_vars[i]
        next_city = city_vars[i+1]
        s.add(Or(
            current_city == next_city,
            *[
                And(current_city == city_to_int[city1], next_city == city_to_int[city2])
                for city1 in cities
                for city2 in direct_flights.get(city1, [])
                if city2 in cities  # ensure city2 is in our list
            ]
        ))
    
    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(days):
            city_int = model.evaluate(city_vars[day]).as_long()
            city_name = int_to_city[city_int]
            itinerary.append({"day": day+1, "city": city_name})
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the function and print the result
result = solve_itinerary()
print(result)