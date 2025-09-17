import json
from z3 import *

def main():
    # Define cities and direct flights
    cities = ['Frankfurt', 'Salzburg', 'Athens', 'Reykjavik', 'Bucharest', 'Valencia', 'Vienna', 'Amsterdam', 'Stockholm', 'Riga']
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    direct_flights = [
        ('Valencia', 'Frankfurt'), ('Vienna', 'Bucharest'), ('Valencia', 'Athens'),
        ('Athens', 'Bucharest'), ('Riga', 'Frankfurt'), ('Stockholm', 'Athens'),
        ('Amsterdam', 'Bucharest'), ('Athens', 'Riga'), ('Amsterdam', 'Frankfurt'),
        ('Stockholm', 'Vienna'), ('Vienna', 'Riga'), ('Amsterdam', 'Reykjavik'),
        ('Reykjavik', 'Frankfurt'), ('Stockholm', 'Amsterdam'), ('Amsterdam', 'Valencia'),
        ('Vienna', 'Frankfurt'), ('Valencia', 'Bucharest'), ('Bucharest', 'Frankfurt'),
        ('Stockholm', 'Frankfurt'), ('Valencia', 'Vienna'), ('Reykjavik', 'Athens'),
        ('Frankfurt', 'Salzburg'), ('Amsterdam', 'Vienna'), ('Stockholm', 'Reykjavik'),
        ('Amsterdam', 'Riga'), ('Stockholm', 'Riga'), ('Vienna', 'Reykjavik'),
        ('Amsterdam', 'Athens'), ('Athens', 'Frankfurt'), ('Vienna', 'Athens'),
        ('Riga', 'Bucharest')
    ]
    
    # Create a set of connected city pairs (sorted)
    connected = set()
    for a, b in direct_flights:
        connected.add(tuple(sorted((a, b))))
    
    # Initialize solver
    solver = Solver()
    
    # Create variables: in_city[city_index][day] for days 0-28 (representing day1 to day29)
    in_city = [[Bool(f'in_{city}_{day}') for day in range(29)] for city in range(len(cities))]
    
    # Constraint: Each day must have at least one city
    for day in range(29):
        solver.add(Or([in_city[i][day] for i in range(len(cities))]))
    
    # Constraint: First and last day must have exactly one city
    for day in [0, 28]:
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                solver.add(Not(And(in_city[i][day], in_city[j][day])))
    
    # Constraint: For other days, at most two cities
    for day in range(1, 28):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                for k in range(j+1, len(cities)):
                    solver.add(Not(And(in_city[i][day], in_city[j][day], in_city[k][day])))
    
    # Constraint: If two cities on same day (non-first/last), they must be connected
    for day in range(1, 28):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                city_i = cities[i]
                city_j = cities[j]
                pair = tuple(sorted((city_i, city_j)))
                if pair not in connected:
                    solver.add(Not(And(in_city[i][day], in_city[j][day])))
    
    # Constraint: Continuity between consecutive days
    for day in range(1, 29):
        prev_day = day - 1
        solver.add(Or([And(in_city[i][prev_day], in_city[i][day]) for i in range(len(cities))]))
    
    # Fixed events constraints
    # Stockholm: days 1-3 (index 0-2)
    solver.add(in_city[city_index['Stockholm']][0])
    solver.add(in_city[city_index['Stockholm']][1])
    solver.add(in_city[city_index['Stockholm']][2])
    
    # Valencia: days 5-6 (index 4-5)
    solver.add(in_city[city_index['Valencia']][4])
    solver.add(in_city[city_index['Valencia']][5])
    
    # Vienna: days 6-10 (index 5-9)
    for day in range(5, 10):
        solver.add(in_city[city_index['Vienna']][day])
    
    # Athens: days 14-18 (index 13-17)
    for day in range(13, 18):
        solver.add(in_city[city_index['Athens']][day])
    
    # Riga: days 18-20 (index 17-19)
    for day in range(17, 20):
        solver.add(in_city[city_index['Riga']][day])
    
    # Total days per city
    total_days = {
        'Frankfurt': 4,
        'Salzburg': 5,
        'Athens': 5,
        'Reykjavik': 5,
        'Bucharest': 3,
        'Valencia': 2,
        'Vienna': 5,
        'Amsterdam': 3,
        'Stockholm': 3,
        'Riga': 3
    }
    
    for city, count in total_days.items():
        idx = city_index[city]
        solver.add(Sum([If(in_city[idx][day], 1, 0) for day in range(29)]) == count)
    
    # Check and get model
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        current_city = None
        start_day = 0
        
        for day in range(29):
            day_cities = []
            for i, city in enumerate(cities):
                if is_true(model.eval(in_city[i][day])):
                    day_cities.append(city)
            
            # On travel days, we're in two cities; use the first one for itinerary display
            primary_city = day_cities[0] if day_cities else None
            
            if primary_city != current_city:
                if current_city is not None:
                    itinerary.append({
                        'day_range': f"Day {start_day+1}-{day}",
                        'place': current_city
                    })
                current_city = primary_city
                start_day = day
        
        # Add the last stay
        if current_city is not None:
            itinerary.append({
                'day_range': f"Day {start_day+1}-29",
                'place': current_city
            })
        
        print(json.dumps({'itinerary': itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()