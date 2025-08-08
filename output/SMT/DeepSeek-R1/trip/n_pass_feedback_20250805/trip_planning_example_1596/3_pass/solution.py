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
        "Munich": [18, 20],
        "Warsaw": [25, 29],
        "Budapest": [9, 13],
        "Stockholm": [17, 18],
        "Edinburgh": [1, 5]
    }
    
    flights_str = "Budapest and Munich, Bucharest and Riga, Munich and Krakow, Munich and Warsaw, Munich and Bucharest, Edinburgh and Stockholm, Barcelona and Warsaw, Edinburgh and Krakow, Barcelona and Munich, Stockholm and Krakow, Budapest and Vienna, Barcelona and Stockholm, Stockholm and Munich, Edinburgh and Budapest, Barcelona and Riga, Edinburgh and Barcelona, Vienna and Riga, Barcelona and Budapest, Bucharest and Warsaw, Vienna and Krakow, Edinburgh and Munich, Barcelona and Bucharest, Edinburgh and Riga, Vienna and Stockholm, Warsaw and Krakow, Barcelona and Krakow, from Riga to Munich, Vienna and Bucharest, Budapest and Warsaw, Vienna and Warsaw, Barcelona and Vienna, Budapest and Bucharest, Vienna and Munich, Riga and Warsaw, Stockholm and Riga, Stockholm and Warsaw"
    flight_tokens = flights_str.split(', ')
    directed_flights = set()
    for token in flight_tokens:
        if ' and ' in token:
            a, b = token.split(' and ')
            directed_flights.add((a.strip(), b.strip()))
            directed_flights.add((b.strip(), a.strip()))
        elif ' to ' in token:
            parts = token.split()
            directed_flights.add((parts[1].strip(), parts[-1].strip()))
            directed_flights.add((parts[-1].strip(), parts[1].strip()))
    
    City = Datatype('City')
    for c in cities:
        City.declare(c)
    City = City.create()
    city_to_name = {getattr(City, c): c for c in cities}
    
    base_city = [Const(f'base_city_{i}', City) for i in range(32)]
    evening_city = [Const(f'evening_city_{i}', City) for i in range(32)]
    
    s = Solver()
    
    # Continuity constraints
    for i in range(31):
        s.add(base_city[i+1] == evening_city[i])
    
    # Flight constraints
    flight_list = []
    for (a, b) in directed_flights:
        flight_list.append((getattr(City, a), getattr(City, b)))
    
    for i in range(32):
        base = base_city[i]
        evening = evening_city[i]
        s.add(Or(base == evening, Or([And(base == a, evening == b) for (a, b) in flight_list])))
    
    # Total stay constraints
    for city, days in required_stays.items():
        c_const = getattr(City, city)
        total_days = Sum([If(base_city[i] == c_const, 1, 0) for i in range(32)] + 
                       [If(And(evening_city[i] == c_const, base_city[i] != c_const), 1, 0) for i in range(32)])
        s.add(total_days == days)
    
    # Event constraints
    for city, (start, end) in events.items():
        c_const = getattr(City, city)
        s.add(Or([Or(base_city[day-1] == c_const, 
                  And(evening_city[day-1] == c_const, base_city[day-1] != c_const)) 
               for day in range(start, end+1)]))
    
    # Fixed base city assignments during events
    for day in range(1, 6):  # Edinburgh: days 1-5
        s.add(base_city[day-1] == City.Edinburgh)
    for day in range(9, 14):  # Budapest: days 9-13
        s.add(base_city[day-1] == City.Budapest)
    s.add(base_city[16] == City.Stockholm)  # Stockholm: day 17
    s.add(base_city[17] == City.Stockholm)  # Stockholm: day 18
    for day in range(18, 21):  # Munich: days 18-20
        s.add(base_city[day-1] == City.Munich)
    for day in range(25, 30):  # Warsaw: days 25-29
        s.add(base_city[day-1] == City.Warsaw)
    
    # Flight day constraint
    flight_days = [If(base_city[i] != evening_city[i], 1, 0) for i in range(32)]
    s.add(Sum(flight_days) == 9)
    
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in range(1, 33):
            idx = day - 1
            base = model.eval(base_city[idx])
            base_name = city_to_name[base]
            itinerary.append({"day": day, "place": base_name})
            if model.eval(base_city[idx] != evening_city[idx]):
                evening = model.eval(evening_city[idx])
                evening_name = city_to_name[evening]
                itinerary.append({"day": day, "place": evening_name})
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()