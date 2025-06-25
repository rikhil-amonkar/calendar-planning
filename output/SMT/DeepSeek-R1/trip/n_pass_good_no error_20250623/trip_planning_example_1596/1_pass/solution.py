from z3 import Int, And, Or, Distinct, Not, If, Solver, sat

def main():
    cities = ['Edinburgh', 'Bucharest', 'Krakow', 'Munich', 'Warsaw', 'Budapest', 'Stockholm', 'Riga', 'Vienna', 'Barcelona']
    Durations = {
        'Edinburgh': 5,
        'Bucharest': 2,
        'Krakow': 4,
        'Munich': 3,
        'Warsaw': 5,
        'Budapest': 5,
        'Stockholm': 2,
        'Riga': 5,
        'Vienna': 5,
        'Barcelona': 5
    }
    Fixed_start = {
        'Budapest': 9,
        'Stockholm': 17,
        'Munich': 18,
        'Warsaw': 25
    }

    flights_str = """Budapest and Munich, Bucharest and Riga, Munich and Krakow, Munich and Warsaw, Munich and Bucharest, Edinburgh and Stockholm, Barcelona and Warsaw, Edinburgh and Krakow, Barcelona and Munich, Stockholm and Krakow, Budapest and Vienna, Barcelona and Stockholm, Stockholm and Munich, Edinburgh and Budapest, Barcelona and Riga, Edinburgh and Barcelona, Vienna and Riga, Barcelona and Budapest, Bucharest and Warsaw, Vienna and Krakow, Edinburgh and Munich, Barcelona and Bucharest, Edinburgh and Riga, Vienna and Stockholm, Warsaw and Krakow, Barcelona and Krakow, from Riga to Munich, Vienna and Bucharest, Budapest and Warsaw, Vienna and Warsaw, Barcelona and Vienna, Budapest and Bucharest, Vienna and Munich, Riga and Warsaw, Stockholm and Riga, Stockholm and Warsaw"""
    flight_pairs = []
    for s in flights_str.split(','):
        s = s.strip()
        if s.startswith("from"):
            parts = s.split()
            city1 = parts[1]
            city2 = parts[3]
            flight_pairs.append((city1, city2))
        else:
            parts = s.split(' and ')
            if len(parts) >= 2:
                city1 = parts[0].strip()
                city2 = parts[1].strip()
                flight_pairs.append((city1, city2))
    allowed_flights = set()
    for (a, b) in flight_pairs:
        allowed_flights.add((a, b))
        allowed_flights.add((b, a))
    
    s = Solver()
    
    start = {}
    for city in cities:
        if city in Fixed_start:
            start[city] = Fixed_start[city]
        else:
            start[city] = Int(f'start_{city}')
    
    position = {}
    for city in cities:
        position[city] = Int(f'pos_{city}')
    
    s.add(Distinct([position[city] for city in cities]))
    for city in cities:
        s.add(position[city] >= 0)
        s.add(position[city] < 10)
    
    first_city_constraint = Or([And(position[city] == 0, start[city] == 1) for city in cities])
    s.add(first_city_constraint)
    
    last_city_constraint = Or([And(position[city] == 9, start[city] + Durations[city] - 1 == 32) for city in cities])
    s.add(last_city_constraint)
    
    for i in range(0, 9):
        for c1 in cities:
            for c2 in cities:
                if c1 == c2:
                    continue
                cond = And(position[c1] == i, position[c2] == i+1)
                s.add(If(cond, start[c2] == start[c1] + Durations[c1] - 1, True))
                if (c1, c2) not in allowed_flights:
                    s.add(Not(cond))
    
    s.add(start['Edinburgh'] <= 5)
    
    for city in cities:
        if city not in Fixed_start:
            s.add(start[city] >= 1)
            s.add(start[city] <= 32 - (Durations[city] - 1))
    
    if s.check() == sat:
        m = s.model()
        start_vals = {}
        pos_vals = {}
        for city in cities:
            if city in Fixed_start:
                start_vals[city] = Fixed_start[city]
            else:
                start_vals[city] = m.evaluate(start[city]).as_long()
            pos_vals[city] = m.evaluate(position[city]).as_long()
        
        sequence = sorted(cities, key=lambda city: pos_vals[city])
        
        itinerary_list = []
        for i, city in enumerate(sequence):
            s_val = start_vals[city]
            d = Durations[city]
            e_val = s_val + d - 1
            if d > 1:
                itinerary_list.append({"day_range": f"Day {s_val}-{e_val}", "place": city})
            else:
                itinerary_list.append({"day_range": f"Day {s_val}", "place": city})
            if i < len(sequence) - 1:
                itinerary_list.append({"day_range": f"Day {e_val}", "place": city})
                next_city = sequence[i+1]
                itinerary_list.append({"day_range": f"Day {e_val}", "place": next_city})
        
        result = {"itinerary": itinerary_list}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()