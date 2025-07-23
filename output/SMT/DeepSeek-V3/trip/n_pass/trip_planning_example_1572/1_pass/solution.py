from z3 import *

def solve_itinerary():
    # Cities involved
    cities = ['Lyon', 'Paris', 'Riga', 'Berlin', 'Stockholm', 'Zurich', 'Nice', 'Seville', 'Milan', 'Naples']
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights: list of tuples (city1, city2)
    direct_flights = [
        ('Paris', 'Stockholm'), ('Seville', 'Paris'), ('Naples', 'Zurich'), ('Nice', 'Riga'),
        ('Berlin', 'Milan'), ('Paris', 'Zurich'), ('Paris', 'Nice'), ('Milan', 'Paris'),
        ('Milan', 'Riga'), ('Paris', 'Lyon'), ('Milan', 'Naples'), ('Paris', 'Riga'),
        ('Berlin', 'Stockholm'), ('Stockholm', 'Riga'), ('Nice', 'Zurich'), ('Milan', 'Zurich'),
        ('Lyon', 'Nice'), ('Zurich', 'Stockholm'), ('Zurich', 'Riga'), ('Berlin', 'Naples'),
        ('Milan', 'Stockholm'), ('Berlin', 'Zurich'), ('Milan', 'Seville'), ('Paris', 'Naples'),
        ('Berlin', 'Riga'), ('Nice', 'Stockholm'), ('Berlin', 'Paris'), ('Nice', 'Naples'),
        ('Berlin', 'Nice')
    ]
    
    # Create a set of direct flight pairs in both directions
    flight_pairs = set()
    for a, b in direct_flights:
        flight_pairs.add((a, b))
        flight_pairs.add((b, a))
    
    # Z3 solver
    s = Solver()
    
    # Variables: day_1 to day_23, each is an integer representing the city index
    days = [Int(f'day_{i}') for i in range(1, 24)]  # days 1..23
    
    # Each day's variable must be a valid city index (0..9)
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Fixed constraints
    # Berlin: wedding between day 1 and 2 (so days 1 and 2 are Berlin)
    s.add(days[0] == city_map['Berlin'])
    s.add(days[1] == city_map['Berlin'])
    
    # Stockholm: annual show from day 20 to 22 (days 20, 21, 22)
    s.add(days[19] == city_map['Stockholm'])
    s.add(days[20] == city_map['Stockholm'])
    s.add(days[21] == city_map['Stockholm'])
    
    # Nice: workshop between day 12 and 13 (days 12, 13)
    s.add(days[11] == city_map['Nice'])
    s.add(days[12] == city_map['Nice'])
    
    # Transition constraints: consecutive days must be the same city or have a direct flight
    for i in range(len(days) - 1):
        current_city = days[i]
        next_city = days[i + 1]
        # Either stay in the same city or take a direct flight
        same_city = current_city == next_city
        flight_possible = Or([And(current_city == city_map[a], next_city == city_map[b]) for a, b in flight_pairs])
        s.add(Or(same_city, flight_possible))
    
    # Duration constraints for each city
    # Lyon: 3 days
    lyon_days = Sum([If(days[i] == city_map['Lyon'], 1, 0) for i in range(23)])
    s.add(lyon_days == 3)
    
    # Paris: 5 days
    paris_days = Sum([If(days[i] == city_map['Paris'], 1, 0) for i in range(23)])
    s.add(paris_days == 5)
    
    # Riga: 2 days
    riga_days = Sum([If(days[i] == city_map['Riga'], 1, 0) for i in range(23)])
    s.add(riga_days == 2)
    
    # Berlin: 2 days (already covered by days 1 and 2)
    berlin_days = Sum([If(days[i] == city_map['Berlin'], 1, 0) for i in range(23)])
    s.add(berlin_days == 2)
    
    # Stockholm: 3 days (already days 20-22)
    stockholm_days = Sum([If(days[i] == city_map['Stockholm'], 1, 0) for i in range(23)])
    s.add(stockholm_days == 3)
    
    # Zurich: 5 days
    zurich_days = Sum([If(days[i] == city_map['Zurich'], 1, 0) for i in range(23)])
    s.add(zurich_days == 5)
    
    # Nice: 2 days (days 12-13)
    nice_days = Sum([If(days[i] == city_map['Nice'], 1, 0) for i in range(23)])
    s.add(nice_days == 2)
    
    # Seville: 3 days
    seville_days = Sum([If(days[i] == city_map['Seville'], 1, 0) for i in range(23)])
    s.add(seville_days == 3)
    
    # Milan: 3 days
    milan_days = Sum([If(days[i] == city_map['Milan'], 1, 0) for i in range(23)])
    s.add(milan_days == 3)
    
    # Naples: 4 days
    naples_days = Sum([If(days[i] == city_map['Naples'], 1, 0) for i in range(23)])
    s.add(naples_days == 4)
    
    # Check and get model
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(23):
            day_num = i + 1
            city_idx = m.evaluate(days[i]).as_long()
            city = cities[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Execute and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))