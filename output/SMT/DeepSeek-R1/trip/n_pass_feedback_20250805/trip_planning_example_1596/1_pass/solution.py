from z3 import *
import json

def main():
    # Cities and required stay days
    cities = ["Bucharest", "Krakow", "Munich", "Barcelona", "Warsaw", 
              "Budapest", "Stockholm", "Riga", "Edinburgh", "Vienna"]
    required_stays = {
        "Bucharest": 2,
        "Krakow": 4,
        "Munich": 3,
        "Barcelona": 5,
        "Warsaw": 5,
        "Budapest": 5,
        "Stockholm": 2,
        "Riga": 5,
        "Edinburgh": 5,
        "Vienna": 5
    }
    
    # Event constraints: city -> [start_day, end_day]
    events = {
        "Munich": [18, 20],
        "Warsaw": [25, 29],
        "Budapest": [9, 13],
        "Stockholm": [17, 18],
        "Edinburgh": [1, 5]
    }
    
    # Parse direct flights
    flights_str = "Budapest and Munich, Bucharest and Riga, Munich and Krakow, Munich and Warsaw, Munich and Bucharest, Edinburgh and Stockholm, Barcelona and Warsaw, Edinburgh and Krakow, Barcelona and Munich, Stockholm and Krakow, Budapest and Vienna, Barcelona and Stockholm, Stockholm and Munich, Edinburgh and Budapest, Barcelona and Riga, Edinburgh and Barcelona, Vienna and Riga, Barcelona and Budapest, Bucharest and Warsaw, Vienna and Krakow, Edinburgh and Munich, Barcelona and Bucharest, Edinburgh and Riga, Vienna and Stockholm, Warsaw and Krakow, Barcelona and Krakow, from Riga to Munich, Vienna and Bucharest, Budapest and Warsaw, Vienna and Warsaw, Barcelona and Vienna, Budapest and Bucharest, Vienna and Munich, Riga and Warsaw, Stockholm and Riga, Stockholm and Warsaw"
    flight_tokens = flights_str.split(', ')
    direct_flights_py = set()
    for token in flight_tokens:
        if ' and ' in token:
            parts = token.split(' and ')
            a = parts[0].strip()
            b = parts[1].strip()
            direct_flights_py.add((a, b))
        elif ' to ' in token:
            parts = token.split()
            a = parts[1].strip()
            b = parts[-1].strip()
            direct_flights_py.add((a, b))
    
    # Create directed flights set (both directions)
    directed_flights = set()
    for (a, b) in direct_flights_py:
        directed_flights.add((a, b))
        directed_flights.add((b, a))
    
    # Define Z3 City datatype
    City = Datatype('City')
    for c in cities:
        City.declare(c)
    City = City.create()
    city_constants = [getattr(City, c) for c in cities]
    
    # Mapping from Z3 constant to city name
    city_to_name = {}
    for c in cities:
        city_to_name[getattr(City, c)] = c
    
    # Create base and evening city variables for 32 days (index 0 to 31)
    base_city = [Const('base_city_%d' % i, City) for i in range(32)]
    evening_city = [Const('evening_city_%d' % i, City) for i in range(32)]
    
    s = Solver()
    
    # Continuity constraints: base_city[i+1] == evening_city[i] for i in 0 to 30
    for i in range(31):
        s.add(base_city[i+1] == evening_city[i])
    
    # Flight constraints: for each day i, either base_city[i] == evening_city[i] or (base_city[i], evening_city[i]) is in directed_flights
    directed_flights_z3 = set()
    for (a_str, b_str) in directed_flights:
        a_const = getattr(City, a_str)
        b_const = getattr(City, b_str)
        directed_flights_z3.add((a_const, b_const))
    
    for i in range(32):
        base = base_city[i]
        evening = evening_city[i]
        no_flight = (base == evening)
        flight_possible = Or([And(base == a, evening == b) for (a, b) in directed_flights_z3])
        s.add(Or(no_flight, flight_possible))
    
    # Total stay constraints for each city
    for c_str in cities:
        c_const = getattr(City, c_str)
        total_base = 0
        total_evening_flight = 0
        for i in range(32):
            total_base += If(base_city[i] == c_const, 1, 0)
            total_evening_flight += If(And(evening_city[i] == c_const, base_city[i] != c_const), 1, 0)
        total_days = total_base + total_evening_flight
        s.add(total_days == required_stays[c_str])
    
    # Event constraints: for each event city, at least one day in the interval must have presence
    for city, (start, end) in events.items():
        c_const = getattr(City, city)
        conds = []
        # Convert day numbers to indices (1-indexed to 0-indexed)
        for day in range(start, end+1):
            idx = day - 1
            in_city = Or(base_city[idx] == c_const, 
                         And(evening_city[idx] == c_const, base_city[idx] != c_const))
            conds.append(in_city)
        s.add(Or(conds))
    
    # Check and get model
    if s.check() == sat:
        model = s.model()
        itinerary_list = []
        for day in range(1, 33):
            idx = day - 1
            base_val = model[base_city[idx]]
            base_name = city_to_name[base_val]
            itinerary_list.append({"day": day, "place": base_name})
            evening_val = model[evening_city[idx]]
            if model.eval(base_city[idx] != evening_city[idx]):
                evening_name = city_to_name[evening_val]
                itinerary_list.append({"day": day, "place": evening_name})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()