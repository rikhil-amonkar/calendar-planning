from z3 import *

def solve_itinerary():
    # Cities involved
    cities = ['Prague', 'Brussels', 'Riga', 'Munich', 'Seville', 'Stockholm', 'Istanbul', 'Amsterdam', 'Vienna', 'Split']
    
    # Direct flights as a set of tuples for easier checking
    flight_pairs = [
        ('Riga', 'Stockholm'), ('Stockholm', 'Riga'),
        ('Stockholm', 'Brussels'), ('Brussels', 'Stockholm'),
        ('Istanbul', 'Munich'), ('Munich', 'Istanbul'),
        ('Istanbul', 'Riga'), ('Riga', 'Istanbul'),
        ('Prague', 'Split'), ('Split', 'Prague'),
        ('Vienna', 'Brussels'), ('Brussels', 'Vienna'),
        ('Vienna', 'Riga'), ('Riga', 'Vienna'),
        ('Split', 'Stockholm'), ('Stockholm', 'Split'),
        ('Munich', 'Amsterdam'), ('Amsterdam', 'Munich'),
        ('Split', 'Amsterdam'), ('Amsterdam', 'Split'),
        ('Amsterdam', 'Stockholm'), ('Stockholm', 'Amsterdam'),
        ('Amsterdam', 'Riga'), ('Riga', 'Amsterdam'),
        ('Vienna', 'Stockholm'), ('Stockholm', 'Vienna'),
        ('Vienna', 'Istanbul'), ('Istanbul', 'Vienna'),
        ('Vienna', 'Seville'), ('Seville', 'Vienna'),
        ('Istanbul', 'Amsterdam'), ('Amsterdam', 'Istanbul'),
        ('Munich', 'Brussels'), ('Brussels', 'Munich'),
        ('Prague', 'Munich'), ('Munich', 'Prague'),
        ('Riga', 'Munich'), ('Munich', 'Riga'),
        ('Prague', 'Amsterdam'), ('Amsterdam', 'Prague'),
        ('Prague', 'Brussels'), ('Brussels', 'Prague'),
        ('Prague', 'Istanbul'), ('Istanbul', 'Prague'),
        ('Vienna', 'Prague'), ('Prague', 'Vienna'),
        ('Munich', 'Split'), ('Split', 'Munich'),
        ('Vienna', 'Amsterdam'), ('Amsterdam', 'Vienna'),
        ('Prague', 'Stockholm'), ('Stockholm', 'Prague'),
        ('Brussels', 'Seville'), ('Seville', 'Brussels'),
        ('Munich', 'Stockholm'), ('Stockholm', 'Munich'),
        ('Istanbul', 'Brussels'), ('Brussels', 'Istanbul'),
        ('Amsterdam', 'Seville'), ('Seville', 'Amsterdam'),
        ('Vienna', 'Munich'), ('Munich', 'Vienna'),
        ('Munich', 'Seville'), ('Seville', 'Munich'),
        ('Riga', 'Brussels'), ('Brussels', 'Riga'),
        ('Prague', 'Riga'), ('Riga', 'Prague'),
        ('Vienna', 'Split'), ('Split', 'Vienna')
    ]
    
    # Create a dictionary for direct flights
    direct_flights = {city: set() for city in cities}
    for a, b in flight_pairs:
        if a in cities and b in cities:
            direct_flights[a].add(b)
            direct_flights[b].add(a)
    
    # Required days per city
    required_days = {
        'Prague': 5,
        'Brussels': 2,
        'Riga': 2,
        'Munich': 2,
        'Seville': 3,
        'Stockholm': 2,
        'Istanbul': 2,
        'Amsterdam': 3,
        'Vienna': 5,
        'Split': 3
    }
    # Correct Vienna's spelling
    required_days['Vienna'] = required_days.pop('Vienna', 5)
    
    # Create Z3 solver
    s = Solver()
    
    # Create variables: day[i] is the city visited on day i+1 (days are 1-based)
    days = [Int('day_%d' % (i+1)) for i in range(20)]
    city_map = {city: idx for idx, city in enumerate(cities)}
    
    # Each day variable must be a valid city index
    for day in days:
        s.add(day >= 0, day < len(cities))
    
    # Function to get city name from index
    def city_name(index):
        return cities[index]
    
    # Constraint: Each city's total days must match required_days
    for city in cities:
        count = 0
        for day in days:
            count += If(day == city_map[city], 1, 0)
        s.add(count == required_days[city])
    
    # Constraint: Consecutive days must be same city or have a direct flight
    for i in range(19):
        current_city = days[i]
        next_city = days[i+1]
        # Either same city or direct flight exists
        same_city = (current_city == next_city)
        # Check for direct flight
        flight_exists = False
        for city_a in cities:
            for city_b in direct_flights[city_a]:
                flight_exists = Or(flight_exists, And(current_city == city_map[city_a], next_city == city_map[city_b]))
        s.add(Or(same_city, flight_exists))
    
    # Special constraints:
    # 1. Prague: 5 days, with show between day 5-9 (so days 5-9 must be Prague)
    for day_idx in [4, 5, 6, 7, 8]:  # 0-based days 5-9 are indices 4-8
        s.add(days[day_idx] == city_map['Prague'])
    
    # 2. Riga: meet friends between day 15-16 (days 15 and/or 16)
    s.add(Or(days[14] == city_map['Riga'], days[15] == city_map['Riga']))
    
    # 3. Stockholm conference on day 16-17 (days 16 and 17)
    s.add(days[15] == city_map['Stockholm'])  # day 16 is index 15
    s.add(days[16] == city_map['Stockholm'])  # day 17 is index 16
    
    # 4. Vienna: meet friend between day 1-5 (days 1-5)
    s.add(Or([days[i] == city_map['Vienna'] for i in range(5)]))
    
    # 5. Split: visit relatives between day 11-13 (days 11-13, indices 10-12)
    s.add(Or([days[i] == city_map['Split'] for i in range(10, 13)]))
    
    # Solve the model
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(20):
            city_idx = model.evaluate(days[i]).as_long()
            itinerary.append({'day': i+1, 'city': cities[city_idx]})
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Generate the itinerary
itinerary = solve_itinerary()
print(itinerary)