from z3 import *
import json

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Reykjavik': 4,
        'Riga': 2,
        'Oslo': 3,
        'Lyon': 5,
        'Dubrovnik': 2,
        'Madrid': 2,
        'Warsaw': 4,
        'London': 3
    }
    
    # Corrected direct flight connections (undirected)
    flight_pairs = [
        ('Warsaw', 'Reykjavik'),
        ('Oslo', 'Madrid'),
        ('Warsaw', 'Riga'),
        ('Lyon', 'London'),
        ('Madrid', 'London'),
        ('Warsaw', 'London'),
        ('Reykjavik', 'Madrid'),
        ('Warsaw', 'Oslo'),
        ('Oslo', 'Dubrovnik'),
        ('Oslo', 'Reykjavik'),
        ('Riga', 'Oslo'),
        ('Oslo', 'Lyon'),
        ('Oslo', 'London'),
        ('London', 'Reykjavik'),
        ('Warsaw', 'Madrid'),
        ('Madrid', 'Lyon'),
        ('Dubrovnik', 'Madrid')
    ]
    
    # Create a set of all possible direct flight connections (both directions)
    allowed_transitions = set()
    for city1, city2 in flight_pairs:
        allowed_transitions.add((city1, city2))
        allowed_transitions.add((city2, city1))
    
    # Days are 1..18
    days = 18
    city_names = sorted(cities.keys())
    
    # Create Z3 variables: assign each day to a city.
    assignments = [Int(f'day_{i}') for i in range(1, days+1)]
    
    # City to integer mapping for Z3
    city_to_int = {city: idx for idx, city in enumerate(city_names, 1)}
    int_to_city = {idx: city for city, idx in city_to_int.items()}
    
    solver = Solver()
    
    # Each day's assignment must be a valid city (1..8)
    for day in assignments:
        solver.add(day >= 1, day <= 8)
    
    # Add constraints for the number of days in each city.
    for city, required_days in cities.items():
        city_code = city_to_int[city]
        solver.add(Sum([If(day == city_code, 1, 0) for day in assignments]) == required_days)
    
    # Transition constraints: consecutive days must be either the same city or connected by a flight.
    for i in range(days - 1):
        current_day = assignments[i]
        next_day = assignments[i+1]
        # Either same city or connected by a flight.
        solver.add(Or(
            current_day == next_day,
            *[
                And(current_day == city_to_int[city1], next_day == city_to_int[city2])
                for (city1, city2) in allowed_transitions
            ]
        ))
    
    # Special constraints:
    # 1. Meet friend in Riga between day 4 and day 5 (so day 4 or 5 must be Riga)
    solver.add(Or(assignments[3] == city_to_int['Riga'], assignments[4] == city_to_int['Riga']))
    
    # 2. Wedding in Dubrovnik between day 7 and day 8 (so day 7 or 8 must be Dubrovnik)
    solver.add(Or(assignments[6] == city_to_int['Dubrovnik'], assignments[7] == city_to_int['Dubrovnik']))
    
    # Add some flexibility to help the solver find a solution
    # For example, require at least 2 consecutive days in some cities
    for city in ['Reykjavik', 'Lyon', 'Warsaw']:
        city_code = city_to_int[city]
        solver.add(Or(
            *[And(assignments[i] == city_code, assignments[i+1] == city_code) 
              for i in range(days - 1)]
        ))
    
    # Check if the problem is satisfiable.
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_code = model.evaluate(assignments[i]).as_long()
            city = int_to_city[city_code]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify the itinerary meets all constraints.
        # Check total days per city.
        city_days = {city: 0 for city in city_names}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        for city, required_days in cities.items():
            assert city_days[city] == required_days, f"City {city} has {city_days[city]} days instead of {required_days}"
        
        # Check transitions.
        for i in range(days - 1):
            current_city = itinerary[i]['place']
            next_city = itinerary[i+1]['place']
            if current_city != next_city:
                assert (current_city, next_city) in allowed_transitions or (next_city, current_city) in allowed_transitions, \
                    f"Invalid transition from {current_city} to {next_city} on days {i+1} to {i+2}"
        
        # Check special constraints.
        # Riga between day 4 and 5.
        assert itinerary[3]['place'] == 'Riga' or itinerary[4]['place'] == 'Riga', "Riga not visited on day 4 or 5"
        # Dubrovnik between day 7 and 8.
        assert itinerary[6]['place'] == 'Dubrovnik' or itinerary[7]['place'] == 'Dubrovnik', "Dubrovnik not visited on day 7 or 8"
        
        # Convert itinerary to the required JSON format.
        result = {'itinerary': itinerary}
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No valid itinerary found"}, indent=2)

# Execute the function and print the result.
print(solve_itinerary())