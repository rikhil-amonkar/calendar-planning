from z3 import *
import json

def main():
    cities = ["Bucharest", "Krakow", "Munich", "Barcelona", "Warsaw", 
              "Budapest", "Stockholm", "Riga", "Edinburgh", "Vienna"]
    required_stays = {
        "Bucharest": 2, "Krakow": 4, "Munich": 3, "Barcelona": 5,
        "Warsaw": 5, "Budapest": 5, "Stockholm": 2, "Riga": 5,
        "Edinburgh": 5, "Vienna": 5
    }
    
    events = {
        "Edinburgh": [1, 5],
        "Budapest": [9, 13],
        "Stockholm": [17, 18],
        "Munich": [18, 20],
        "Warsaw": [25, 29]
    }
    
    flights_str = "Budapest and Munich, Bucharest and Riga, Munich and Krakow, Munich and Warsaw, Munich and Bucharest, Edinburgh and Stockholm, Barcelona and Warsaw, Edinburgh and Krakow, Barcelona and Munich, Stockholm and Krakow, Budapest and Vienna, Barcelona and Stockholm, Stockholm and Munich, Edinburgh and Budapest, Barcelona and Riga, Edinburgh and Barcelona, Vienna and Riga, Barcelona and Budapest, Bucharest and Warsaw, Vienna and Krakow, Edinburgh and Munich, Barcelona and Bucharest, Edinburgh and Riga, Vienna and Stockholm, Warsaw and Krakow, Barcelona and Krakow, from Riga to Munich, Vienna and Bucharest, Budapest and Warsaw, Vienna and Warsaw, Barcelona and Vienna, Budapest and Bucharest, Vienna and Munich, Riga and Warsaw, Stockholm and Riga, Stockholm and Warsaw"
    flight_tokens = flights_str.split(', ')
    directed_flights = set()
    for token in flight_tokens:
        token = token.strip()
        if token.startswith('from'):
            parts = token.split()
            directed_flights.add((parts[1], parts[3]))
            directed_flights.add((parts[3], parts[1]))
        elif ' and ' in token:
            a, b = token.split(' and ')
            a = a.strip()
            b = b.strip()
            directed_flights.add((a, b))
            directed_flights.add((b, a))
    
    City = Datatype('City')
    for c in cities:
        City.declare(c)
    City = City.create()
    city_map = {c: getattr(City, c) for c in cities}
    name_map = {getattr(City, c): c for c in cities}
    
    base_city = [Const(f'base_{i}', City) for i in range(32)]
    evening_city = [Const(f'evening_{i}', City) for i in range(32)]
    
    s = Solver()
    
    # Start and end constraints
    s.add(base_city[0] == City.Edinburgh)
    s.add(evening_city[31] == City.Riga)
    
    # Continuity between days
    for i in range(31):
        s.add(base_city[i+1] == evening_city[i])
    
    # Flight constraints
    flight_connections = []
    for a, b in directed_flights:
        flight_connections.append((city_map[a], city_map[b]))
    
    for i in range(32):
        base = base_city[i]
        evening = evening_city[i]
        flight_possible = Or([And(base == a, evening == b) for a, b in flight_connections])
        s.add(Or(base == evening, flight_possible))
    
    # Flight day count (must be exactly 9)
    flight_days = [If(base_city[i] != evening_city[i], 1, 0) for i in range(32)]
    s.add(Sum(flight_days) == 9)
    
    # Stay duration constraints
    for city, days in required_stays.items():
        c = city_map[city]
        total_days = Sum(
            [If(base_city[i] == c, 1, 0) for i in range(32)] +
            [If(And(evening_city[i] == c, base_city[i] != c), 1, 0) for i in range(32)]
        )
        s.add(total_days == days)
    
    # Event attendance constraints - must be present EVERY DAY of event
    for city, (start, end) in events.items():
        c = city_map[city]
        for day in range(start, end + 1):
            day_idx = day - 1
            s.add(Or(
                base_city[day_idx] == c,
                evening_city[day_idx] == c
            ))
    
    # Solve and output
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(32):
            base_val = model.eval(base_city[day])
            base_name = name_map[base_val]
            itinerary.append({"day": day+1, "place": base_name})
            
            evening_val = model.eval(evening_city[day])
            if model.eval(base_city[day] != evening_city[day]):
                evening_name = name_map[evening_val]
                itinerary.append({"day": day+1, "place": evening_name})
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()