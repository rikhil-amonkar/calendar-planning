import json
from z3 import *

def main():
    # Define cities and their indices
    cities = ['Prague', 'Brussels', 'Riga', 'Munich', 'Seville', 'Stockholm', 'Istanbul', 'Amsterdam', 'Vienna', 'Split']
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Define direct flights as symmetric pairs
    flight_pairs = [
        ('Riga', 'Stockholm'), ('Stockholm', 'Brussels'), ('Istanbul', 'Munich'),
        ('Istanbul', 'Riga'), ('Prague', 'Split'), ('Vienna', 'Brussels'),
        ('Vienna', 'Riga'), ('Split', 'Stockholm'), ('Munich', 'Amsterdam'),
        ('Split', 'Amsterdam'), ('Amsterdam', 'Stockholm'), ('Amsterdam', 'Riga'),
        ('Vienna', 'Stockholm'), ('Vienna', 'Istanbul'), ('Vienna', 'Seville'),
        ('Istanbul', 'Amsterdam'), ('Munich', 'Brussels'), ('Prague', 'Munich'),
        ('Riga', 'Munich'), ('Prague', 'Amsterdam'), ('Prague', 'Brussels'),
        ('Prague', 'Istanbul'), ('Istanbul', 'Stockholm'), ('Vienna', 'Prague'),
        ('Munich', 'Split'), ('Vienna', 'Amsterdam'), ('Prague', 'Stockholm'),
        ('Brussels', 'Seville'), ('Munich', 'Stockholm'), ('Istanbul', 'Brussels'),
        ('Amsterdam', 'Seville'), ('Vienna', 'Split'), ('Munich', 'Seville'),
        ('Riga', 'Brussels'), ('Prague', 'Riga'), ('Vienna', 'Munich')
    ]
    
    flights = set()
    for city1, city2 in flight_pairs:
        idx1 = city_index[city1]
        idx2 = city_index[city2]
        flights.add((idx1, idx2))
        flights.add((idx2, idx1))
    
    n_days = 20
    n_cities = len(cities)
    
    # Create Z3 solver and variables
    solver = Solver()
    
    # For each day, morning city (index) and travel boolean
    morning_city = [Int(f'morning_city_{i}') for i in range(1, n_days+1)]
    travel = [Bool(f'travel_{i}') for i in range(1, n_days+1)]
    evening_city = [Int(f'evening_city_{i}') for i in range(1, n_days+1)]
    
    # Domain constraints for morning and evening cities
    for i in range(n_days):
        solver.add(And(morning_city[i] >= 0, morning_city[i] < n_cities))
        solver.add(And(evening_city[i] >= 0, evening_city[i] < n_cities))
    
    # Constraints for each day
    for i in range(n_days):
        # If not traveling, evening city equals morning city
        solver.add(Implies(Not(travel[i]), evening_city[i] == morning_city[i]))
        # If traveling, evening city != morning city and there's a direct flight
        solver.add(Implies(travel[i], evening_city[i] != morning_city[i]))
        solver.add(Implies(travel[i], Or([And(morning_city[i] == a, evening_city[i] == b) for (a, b) in flights])))
    
    # Continuity: evening city of day i is morning city of day i+1
    for i in range(n_days-1):
        solver.add(evening_city[i] == morning_city[i+1])
    
    # Total days per city constraints
    city_days = [0] * n_cities
    for c in range(n_cities):
        # Count days in city c: morning presence plus evening presence if traveling
        total = 0
        for i in range(n_days):
            total += If(And(morning_city[i] == c, Not(travel[i])), 1, 0)
            total += If(And(travel[i], evening_city[i] == c), 1, 0)
            total += If(And(travel[i], morning_city[i] == c), 1, 0)
        city_days[c] = total
    
    solver.add(city_days[city_index['Prague']] == 5)
    solver.add(city_days[city_index['Brussels']] == 2)
    solver.add(city_days[city_index['Riga']] == 2)
    solver.add(city_days[city_index['Munich']] == 2)
    solver.add(city_days[city_index['Seville']] == 3)
    solver.add(city_days[city_index['Stockholm']] == 2)
    solver.add(city_days[city_index['Istanbul']] == 2)
    solver.add(city_days[city_index['Amsterdam']] == 3)
    solver.add(city_days[city_index['Vienna']] == 5)
    solver.add(city_days[city_index['Split']] == 3)
    
    # Specific day constraints
    # Prague: must be in Prague on days 5-9 (1-indexed) without travel
    for i in [4,5,6,7,8]:  # indices 4 to 8 for days 5 to 9
        solver.add(morning_city[i] == city_index['Prague'])
        solver.add(Not(travel[i]))
    
    # Riga: must be in Riga on days 15 and 16 without travel
    for i in [14,15]:  # days 15 and 16
        solver.add(morning_city[i] == city_index['Riga'])
        solver.add(Not(travel[i]))
    
    # Stockholm: must be in Stockholm on days 16 and 17 without travel
    for i in [15,16]:  # days 16 and 17
        solver.add(morning_city[i] == city_index['Stockholm'])
        solver.add(Not(travel[i]))
    
    # Vienna: must be in Vienna on at least one day between 1 and 5
    vienna_days = []
    for i in range(0,5):  # days 1 to 5
        vienna_days.append(Or(morning_city[i] == city_index['Vienna'], 
                              And(travel[i], evening_city[i] == city_index['Vienna'])))
    solver.add(Or(vienna_days))
    
    # Split: must be in Split on at least one day between 11 and 13
    split_days = []
    for i in [10,11,12]:  # days 11,12,13
        split_days.append(Or(morning_city[i] == city_index['Split'], 
                             And(travel[i], evening_city[i] == city_index['Split'])))
    solver.add(Or(split_days))
    
    # Check feasibility
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(n_days):
            day_num = i + 1
            morn_city_val = model.evaluate(morning_city[i]).as_long()
            travel_val = is_true(model.evaluate(travel[i]))
            eve_city_val = model.evaluate(evening_city[i]).as_long()
            
            itinerary.append({"day_range": f"Day {day_num}", "place": cities[morn_city_val]})
            if travel_val:
                itinerary.append({"day_range": f"Day {day_num}", "place": cities[eve_city_val]})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No valid itinerary found.')

if __name__ == '__main__':
    main()