from z3 import *
import json

def main():
    # Cities
    cities = ['Dublin', 'Krakow', 'Istanbul', 'Venice', 'Naples', 'Brussels', 'Mykonos', 'Frankfurt']
    city_index = {city: idx for idx, city in enumerate(cities)}
    
    # Direct flights (undirected)
    direct_flights = [
        ('Dublin', 'Brussels'),
        ('Mykonos', 'Naples'),
        ('Venice', 'Istanbul'),
        ('Frankfurt', 'Krakow'),
        ('Naples', 'Dublin'),
        ('Krakow', 'Brussels'),
        ('Naples', 'Istanbul'),
        ('Naples', 'Brussels'),
        ('Istanbul', 'Frankfurt'),
        ('Brussels', 'Frankfurt'),
        ('Istanbul', 'Krakow'),
        ('Istanbul', 'Brussels'),
        ('Venice', 'Frankfurt'),
        ('Naples', 'Frankfurt'),
        ('Dublin', 'Krakow'),
        ('Venice', 'Brussels'),
        ('Naples', 'Venice'),
        ('Istanbul', 'Dublin'),
        ('Venice', 'Dublin'),
        ('Dublin', 'Frankfurt')
    ]
    
    # Build graph of connected cities
    graph = {city: set() for city in cities}
    for a, b in direct_flights:
        graph[a].add(b)
        graph[b].add(a)
    
    # Required days per city
    required_days = {
        'Dublin': 5,
        'Krakow': 4,
        'Istanbul': 3,
        'Venice': 3,
        'Naples': 4,
        'Brussels': 2,
        'Mykonos': 4,
        'Frankfurt': 3
    }
    
    # Z3 solver
    s = Solver()
    
    # Variables: in_city[d][c] is True if we are in city c on day d (1-indexed days, 0-indexed in array)
    in_city = [[Bool(f"day_{d}_{c}") for c in cities] for d in range(21)]
    
    # Constraint: Each day must be in at least one city
    for d in range(21):
        s.add(Or(in_city[d]))
    
    # Constraint: If two cities on same day, they must be connected by direct flight
    for d in range(21):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                city_i = cities[i]
                city_j = cities[j]
                if city_j not in graph[city_i]:
                    s.add(Not(And(in_city[d][i], in_city[d][j])))
    
    # Constraint: At most two cities per day
    for d in range(21):
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                for k in range(j+1, len(cities)):
                    s.add(Not(And(in_city[d][i], in_city[d][j], in_city[d][k])))
    
    # Constraint: Total days per city
    for c_idx, city in enumerate(cities):
        total = Sum([If(in_city[d][c_idx], 1, 0) for d in range(21)])
        s.add(total == required_days[city])
    
    # Specific constraints
    dublin_idx = city_index['Dublin']
    istanbul_idx = city_index['Istanbul']
    mykonos_idx = city_index['Mykonos']
    frankfurt_idx = city_index['Frankfurt']
    
    # Dublin: must be there on days 11-15 (indices 10-14)
    for d in [10, 11, 12, 13, 14]:
        s.add(in_city[d][dublin_idx])
    
    # Istanbul: at least one day between 9-11 (indices 8-10)
    s.add(Or([in_city[d][istanbul_idx] for d in [8, 9, 10]]))
    
    # Mykonos: at least one day between 1-4 (indices 0-3)
    s.add(Or([in_city[d][mykonos_idx] for d in [0, 1, 2, 3]]))
    
    # Frankfurt: at least one day between 15-17 (indices 14-16)
    s.add(Or([in_city[d][frankfurt_idx] for d in [14, 15, 16]]))
    
    # Check and model
    if s.check() == sat:
        m = s.model()
        # Determine presence each day
        itinerary_per_day = []
        for d in range(21):
            cities_today = []
            for c_idx, city in enumerate(cities):
                if is_true(m.evaluate(in_city[d][c_idx])):
                    cities_today.append(city)
            itinerary_per_day.append(cities_today)
        
        # Group days by city for continuous segments
        city_days = {city: [] for city in cities}
        for day_idx, cities_list in enumerate(itinerary_per_day):
            day_num = day_idx + 1
            for city in cities_list:
                city_days[city].append(day_num)
        
        itinerary_list = []
        for city, days in city_days.items():
            days.sort()
            if not days:
                continue
            segments = []
            start = days[0]
            current = start
            for i in range(1, len(days)):
                if days[i] == current + 1:
                    current = days[i]
                else:
                    segments.append((start, current))
                    start = days[i]
                    current = days[i]
            segments.append((start, current))
            
            for seg in segments:
                start_day, end_day = seg
                if start_day == end_day:
                    day_range = f"Day {start_day}"
                else:
                    day_range = f"Day {start_day}-{end_day}"
                itinerary_list.append({"day_range": day_range, "place": city})
        
        # Sort by start day
        itinerary_list.sort(key=lambda x: int(x['day_range'].split(' ')[1].split('-')[0]))
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()