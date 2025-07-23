from z3 import *
import json

def solve_itinerary():
    # Cities
    cities = ['Bucharest', 'Venice', 'Prague', 'Frankfurt', 'Zurich', 'Florence', 'Tallinn']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: list of tuples (from, to)
    direct_flights = [
        ('Prague', 'Tallinn'), ('Prague', 'Zurich'), ('Florence', 'Prague'),
        ('Frankfurt', 'Bucharest'), ('Frankfurt', 'Venice'), ('Prague', 'Bucharest'),
        ('Bucharest', 'Zurich'), ('Tallinn', 'Frankfurt'), ('Zurich', 'Florence'),
        ('Frankfurt', 'Zurich'), ('Zurich', 'Venice'), ('Florence', 'Frankfurt'),
        ('Prague', 'Frankfurt'), ('Tallinn', 'Zurich')
    ]
    # Make it bidirectional
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Create Z3 solver
    solver = Solver()
    
    # Variables: for each day, which city are you in?
    day_city = [Int(f'day_{day}_city') for day in range(1, 27)]  # days 1..26
    
    # Each day_city variable must be between 0 and 6 (index of cities)
    for day in range(26):
        solver.add(day_city[day] >= 0, day_city[day] < len(cities))
    
    # Constraint: consecutive days must be either same city or connected by a direct flight
    for day in range(25):
        current_city_var = day_city[day]
        next_city_var = day_city[day + 1]
        # Either same city or a valid flight
        solver.add(Or(
            current_city_var == next_city_var,
            *[And(current_city_var == city_map[a], next_city_var == city_map[b]) for a, b in flight_pairs]
        ))
    
    # Total days per city constraints
    total_days = [Int(f'total_{city}') for city in cities]
    for city_idx in range(len(cities)):
        solver.add(total_days[city_idx] == Sum([If(day_city[d] == city_idx, 1, 0) for d in range(26)]))
    
    solver.add(total_days[city_map['Bucharest']] == 3)
    solver.add(total_days[city_map['Venice']] == 5)
    solver.add(total_days[city_map['Prague']] == 4)
    solver.add(total_days[city_map['Frankfurt']] == 5)
    solver.add(total_days[city_map['Zurich']] == 5)
    solver.add(total_days[city_map['Florence']] == 5)
    solver.add(total_days[city_map['Tallinn']] == 5)
    
    # Specific date ranges:
    # Venice between day 22-26 (wedding)
    for day in range(21, 26):  # days 22-26 are indices 21-25 in 0-based
        solver.add(day_city[day] == city_map['Venice'])
    
    # Frankfurt show between day 12-16 (indices 11-15)
    for day in range(11, 16):
        solver.add(day_city[day] == city_map['Frankfurt'])
    
    # Tallinn friends between day 8-12 (indices 7-11)
    for day in range(7, 12):
        solver.add(day_city[day] == city_map['Tallinn'])
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for day in range(26):
            city_idx = model.evaluate(day_city[day]).as_long()
            itinerary.append({'day': day + 1, 'city': cities[city_idx]})
        
        # Generate the required JSON
        result = {
            'itinerary': itinerary
        }
        return result
    else:
        return None

# Solve and print the itinerary
itinerary = solve_itinerary()
if itinerary:
    print(json.dumps(itinerary, indent=2))
else:
    print("No valid itinerary found.")