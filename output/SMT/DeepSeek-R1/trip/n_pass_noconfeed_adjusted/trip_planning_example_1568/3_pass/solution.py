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
    
    morning_city = [Int(f'morning_city_{i}') for i in range(1, n_days+1)]
    travel = [Bool(f'travel_{i}') for i in range(1, n_days+1)]
    evening_city = [Int(f'evening_city_{i}') for i in range(1, n_days+1)]
    
    for i in range(n_days):
        solver.add(And(morning_city[i] >= 0, morning_city[i] < n_cities))
        solver.add(And(evening_city[i] >= 0, evening_city[i] < n_cities))
    
    for i in range(n_days):
        solver.add(Implies(Not(travel[i]), evening_city[i] == morning_city[i]))
        solver.add(Implies(travel[i], evening_city[i] != morning_city[i]))
        solver.add(Implies(travel[i], Or([And(morning_city[i] == a, evening_city[i] == b) for (a, b) in flights])))
    
    for i in range(n_days-1):
        solver.add(evening_city[i] == morning_city[i+1])
    
    required_days = [5, 2, 2, 2, 3, 2, 2, 3, 5, 3]
    for c in range(n_cities):
        total_half_days = 0
        for i in range(n_days):
            total_half_days += If(And(morning_city[i] == c, Not(travel[i])), 2, 0)
            total_half_days += If(And(travel[i], morning_city[i] == c), 1, 0)
            total_half_days += If(And(travel[i], evening_city[i] == c), 1, 0)
        solver.add(total_half_days == 2 * required_days[c])
    
    for i in [4, 5, 6, 7, 8]:
        solver.add(morning_city[i] == city_index['Prague'])
        solver.add(Not(travel[i]))
    
    # Revised constraints for Riga and Stockholm
    solver.add(morning_city[14] == city_index['Riga'])  # Day 15
    solver.add(Not(travel[14]))  # No travel on day 15
    solver.add(morning_city[15] == city_index['Riga'])  # Day 16 morning in Riga
    # Allow travel on day 16 to transition to Stockholm
    solver.add(evening_city[15] == city_index['Stockholm'])  # Day 16 evening in Stockholm
    solver.add(travel[15])  # Travel on day 16

    solver.add(morning_city[16] == city_index['Stockholm'])  # Day 17
    solver.add(Not(travel[16]))  # No travel on day 17
    solver.add(morning_city[17] == city_index['Stockholm'])  # Day 18
    solver.add(Not(travel[17]))  # No travel on day 18
    
    vienna_days = []
    for i in range(0, 5):
        vienna_days.append(Or(morning_city[i] == city_index['Vienna'], 
                              And(travel[i], evening_city[i] == city_index['Vienna'])))
    solver.add(Or(vienna_days))
    
    split_days = []
    for i in [10, 11, 12]:
        split_days.append(Or(morning_city[i] == city_index['Split'], 
                             And(travel[i], evening_city[i] == city_index['Split'])))
    solver.add(Or(split_days))
    
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