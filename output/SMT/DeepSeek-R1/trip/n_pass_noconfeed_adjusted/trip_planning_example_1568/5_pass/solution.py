import json
from z3 import *

def main():
    cities = ['Prague', 'Brussels', 'Riga', 'Munich', 'Seville', 'Stockholm', 'Istanbul', 'Amsterdam', 'Vienna', 'Split']
    city_index = {city: idx for idx, city in enumerate(cities)}
    
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
    
    solver = Solver()
    
    # Decision variables
    morning_city = [Int(f'morning_city_{i}') for i in range(n_days)]
    travel = [Bool(f'travel_{i}') for i in range(n_days)]
    evening_city = [Int(f'evening_city_{i}') for i in range(n_days)]
    
    # Domain constraints for cities
    for i in range(n_days):
        solver.add(And(morning_city[i] >= 0, morning_city[i] < n_cities))
        solver.add(And(evening_city[i] >= 0, evening_city[i] < n_cities))
    
    # Travel constraints
    for i in range(n_days):
        solver.add(Implies(Not(travel[i]), morning_city[i] == evening_city[i]))
        solver.add(Implies(travel[i], morning_city[i] != evening_city[i]))
        solver.add(Implies(travel[i], Or([And(morning_city[i] == a, evening_city[i] == b) for (a, b) in flights])))
    
    # Continuity between days
    for i in range(n_days-1):
        solver.add(evening_city[i] == morning_city[i+1])
    
    # Required days per city (full days)
    required_days = [5, 2, 2, 2, 3, 2, 2, 3, 5, 3]
    
    # Count full days in each city
    city_days = [Int(f'city_days_{c}') for c in range(n_cities)]
    for c in range(n_cities):
        total_days = 0
        for i in range(n_days):
            # A full day in city c if no travel and morning city is c
            total_days += If(And(morning_city[i] == c, Not(travel[i])), 1, 0)
        solver.add(city_days[c] == total_days)
        solver.add(city_days[c] == required_days[c])
    
    # Fixed days in Prague (days 5-9)
    for i in range(4, 9):
        solver.add(morning_city[i] == city_index['Prague'])
        solver.add(Not(travel[i]))
    
    # Day 15 in Riga without travel
    solver.add(morning_city[14] == city_index['Riga'])
    solver.add(Not(travel[14]))
    
    # Day 16 travel from Riga to Stockholm
    solver.add(morning_city[15] == city_index['Riga'])
    solver.add(evening_city[15] == city_index['Stockholm'])
    solver.add(travel[15])
    
    # Day 17 morning in Stockholm
    solver.add(morning_city[16] == city_index['Stockholm'])
    
    # Vienna in one of the first five days
    vienna_constraints = []
    for i in range(0, 5):
        vienna_constraints.append(Or(morning_city[i] == city_index['Vienna'], 
                                  evening_city[i] == city_index['Vienna']))
    solver.add(Or(vienna_constraints))
    
    # Split in one of days 11-13
    split_constraints = []
    for i in range(10, 13):
        split_constraints.append(Or(morning_city[i] == city_index['Split'], 
                                 evening_city[i] == city_index['Split']))
    solver.add(Or(split_constraints))
    
    # Check for satisfaction
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(n_days):
            morn_city_val = model.evaluate(morning_city[i]).as_long()
            travel_val = is_true(model.evaluate(travel[i]))
            eve_city_val = model.evaluate(evening_city[i]).as_long()
            
            itinerary.append({"day_range": f"Day {i+1}", "place": cities[morn_city_val]})
            if travel_val:
                itinerary.append({"day_range": f"Day {i+1}", "place": cities[eve_city_val]})
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('No valid itinerary found.')

if __name__ == '__main__':
    main()