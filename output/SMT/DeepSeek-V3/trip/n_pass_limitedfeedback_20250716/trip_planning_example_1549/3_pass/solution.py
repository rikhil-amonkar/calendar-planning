from z3 import *
import json

def solve_itinerary():
    # Cities to visit
    cities = ['Prague', 'Tallinn', 'Warsaw', 'Porto', 'Naples', 'Milan', 'Lisbon', 'Santorini', 'Riga', 'Stockholm']
    
    # Days in each city
    days_in_city = {
        'Prague': 5,
        'Tallinn': 3,
        'Warsaw': 2,
        'Porto': 3,
        'Naples': 5,
        'Milan': 3,
        'Lisbon': 5,
        'Santorini': 5,
        'Riga': 4,
        'Stockholm': 2
    }
    
    # Direct flights (undirected)
    direct_flights = [
        ('Riga', 'Prague'),
        ('Stockholm', 'Milan'),
        ('Riga', 'Milan'),
        ('Lisbon', 'Stockholm'),
        ('Stockholm', 'Santorini'),
        ('Naples', 'Warsaw'),
        ('Lisbon', 'Warsaw'),
        ('Naples', 'Milan'),
        ('Lisbon', 'Naples'),
        ('Riga', 'Tallinn'),
        ('Tallinn', 'Prague'),
        ('Stockholm', 'Warsaw'),
        ('Riga', 'Warsaw'),
        ('Lisbon', 'Riga'),
        ('Riga', 'Stockholm'),
        ('Lisbon', 'Porto'),
        ('Lisbon', 'Prague'),
        ('Milan', 'Porto'),
        ('Prague', 'Milan'),
        ('Lisbon', 'Milan'),
        ('Warsaw', 'Porto'),
        ('Warsaw', 'Tallinn'),
        ('Santorini', 'Milan'),
        ('Stockholm', 'Prague'),
        ('Stockholm', 'Tallinn'),
        ('Warsaw', 'Milan'),
        ('Santorini', 'Naples'),
        ('Warsaw', 'Prague')
    ]
    
    # Create a set of direct flight pairs for easy lookup
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Total days
    total_days = 28
    
    # Create Z3 variables: assign each day to a city
    day_to_city = [Int(f'day_{i}_city') for i in range(1, total_days + 1)]
    
    # City to integer mapping
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}
    
    # Solver
    solver = Solver()
    
    # Each day is assigned to a city index (0..9)
    for day_var in day_to_city:
        solver.add(day_var >= 0, day_var < len(cities))
    
    # Constraints for days in each city
    for city in cities:
        required_days = days_in_city[city]
        city_idx = city_to_int[city]
        solver.add(Sum([If(day_var == city_idx, 1, 0) for day_var in day_to_city]) == required_days)
    
    # Transition constraints: consecutive days must be same city or have a direct flight
    for i in range(total_days - 1):
        current_day = day_to_city[i]
        next_day = day_to_city[i + 1]
        # Either same city or connected by flight
        solver.add(Or(
            current_day == next_day,
            *[And(current_day == city_to_int[a], next_day == city_to_int[b]) for a, b in flight_pairs]
        ))
    
    # Specific constraints:
    # Riga from day 5 to day 8 (days 5,6,7,8)
    for day in [5, 6, 7, 8]:
        solver.add(day_to_city[day - 1] == city_to_int['Riga'])
    
    # Tallinn between day 18 and 20 (days 18,19,20)
    solver.add(day_to_city[17] == city_to_int['Tallinn'])  # day 18
    solver.add(day_to_city[18] == city_to_int['Tallinn'])  # day 19
    solver.add(day_to_city[19] == city_to_int['Tallinn'])  # day 20
    
    # Milan between day 24 and 26 (days 24,25,26)
    solver.add(day_to_city[23] == city_to_int['Milan'])  # day 24
    solver.add(day_to_city[24] == city_to_int['Milan'])  # day 25
    solver.add(day_to_city[25] == city_to_int['Milan'])  # day 26
    
    # Check if the problem is satisfiable
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for day in range(1, total_days + 1):
            city_idx = model.evaluate(day_to_city[day - 1]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({'day': day, 'place': city})
        
        # Verify the solution meets all constraints
        city_days = {city: 0 for city in cities}
        for entry in itinerary:
            city_days[entry['place']] += 1
        
        for city in cities:
            assert city_days[city] == days_in_city[city], f"City {city} has {city_days[city]} days instead of {days_in_city[city]}"
        
        # Check transitions
        for i in range(len(itinerary) - 1):
            current_city = itinerary[i]['place']
            next_city = itinerary[i + 1]['place']
            if current_city != next_city:
                assert (current_city, next_city) in flight_pairs, f"No flight from {current_city} to {next_city} on day {i+1}"
        
        # Check specific day constraints
        assert itinerary[4]['place'] == 'Riga'  # day 5
        assert itinerary[5]['place'] == 'Riga'  # day 6
        assert itinerary[6]['place'] == 'Riga'  # day 7
        assert itinerary[7]['place'] == 'Riga'  # day 8
        
        assert itinerary[17]['place'] == 'Tallinn'  # day 18
        assert itinerary[18]['place'] == 'Tallinn'  # day 19
        assert itinerary[19]['place'] == 'Tallinn'  # day 20
        
        assert itinerary[23]['place'] == 'Milan'  # day 24
        assert itinerary[24]['place'] == 'Milan'  # day 25
        assert itinerary[25]['place'] == 'Milan'  # day 26
        
        # Convert to the required JSON format
        result = {'itinerary': itinerary}
        return result
    else:
        raise Exception("No valid itinerary found")

# Generate the itinerary
itinerary = solve_itinerary()
print(json.dumps(itinerary, indent=2))