import json
from z3 import *

def main():
    n_days = 28
    cities = ['Prague', 'Tallinn', 'Warsaw', 'Porto', 'Naples', 'Milan', 'Lisbon', 'Santorini', 'Riga', 'Stockholm']
    required_days = {
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
    
    direct_flights_list = [
        ('Riga', 'Prague'), ('Stockholm', 'Milan'), ('Riga', 'Milan'), ('Lisbon', 'Stockholm'),
        ('Stockholm', 'Santorini'), ('Naples', 'Warsaw'), ('Lisbon', 'Warsaw'), ('Naples', 'Milan'),
        ('Lisbon', 'Naples'), ('Riga', 'Tallinn'), ('Tallinn', 'Prague'), ('Stockholm', 'Warsaw'),
        ('Riga', 'Warsaw'), ('Lisbon', 'Riga'), ('Riga', 'Stockholm'), ('Lisbon', 'Porto'),
        ('Lisbon', 'Prague'), ('Milan', 'Porto'), ('Prague', 'Milan'), ('Lisbon', 'Milan'),
        ('Warsaw', 'Porto'), ('Warsaw', 'Tallinn'), ('Santorini', 'Milan'), ('Stockholm', 'Prague'),
        ('Stockholm', 'Tallinn'), ('Warsaw', 'Milan'), ('Santorini', 'Naples'), ('Warsaw', 'Prague')
    ]
    
    direct_flights = set()
    for a, b in direct_flights_list:
        direct_flights.add((a, b))
        direct_flights.add((b, a))
    
    s = Solver()
    
    in_city = [[Bool(f'in_day{day+1}_{city}') for city in cities] for day in range(n_days)]
    travel = [Bool(f'travel_{day+1}') for day in range(n_days)]
    
    for day in range(n_days):
        total_cities = Sum([If(in_city[day][i], 1, 0) for i in range(len(cities))])
        s.add(Or(total_cities == 1, total_cities == 2))
        s.add(travel[day] == (total_cities == 2))
        
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                if (cities[i], cities[j]) not in direct_flights:
                    s.add(Not(And(in_city[day][i], in_city[day][j])))
    
    for day in range(n_days-1):
        s.add(Or([And(in_city[day][i], in_city[day+1][i]) for i in range(len(cities))]))
    
    for c_idx, city in enumerate(cities):
        total_days = Sum([If(in_city[day][c_idx], 1, 0) for day in range(n_days)])
        s.add(total_days >= required_days[city])
    
    tallinn_idx = cities.index('Tallinn')
    for day in [17, 18, 19]:
        s.add(in_city[day][tallinn_idx])
    
    riga_idx = cities.index('Riga')
    for day in [4, 5, 6, 7]:
        s.add(in_city[day][riga_idx])
    
    milan_idx = cities.index('Milan')
    for day in [23, 24, 25]:
        s.add(in_city[day][milan_idx])
    
    if s.check() == sat:
        m = s.model()
        actual_presence = []
        for day in range(n_days):
            day_cities = []
            for c_idx in range(len(cities)):
                if m.evaluate(in_city[day][c_idx]):
                    day_cities.append(cities[c_idx])
            actual_presence.append(day_cities)
        
        rep_cities = [None] * n_days
        for day in range(n_days-1):
            common = set(actual_presence[day]) & set(actual_presence[day+1])
            if common:
                rep_cities[day] = sorted(common)[0]
            else:
                rep_cities[day] = actual_presence[day][0]
        common_last = set(actual_presence[n_days-1]) & set(actual_presence[n_days-2])
        if common_last:
            rep_cities[n_days-1] = sorted(common_last)[0]
        else:
            rep_cities[n_days-1] = actual_presence[n_days-1][0]
        
        itinerary = []
        start = 0
        current = rep_cities[0]
        for day in range(1, n_days):
            if rep_cities[day] != current:
                itinerary.append({
                    "day_range": f"Day {start+1}-{day}",
                    "place": current
                })
                start = day
                current = rep_cities[day]
        itinerary.append({
            "day_range": f"Day {start+1}-{n_days}",
            "place": current
        })
        
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()