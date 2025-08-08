from z3 import *

def main():
    cities = ['Bucharest', 'Krakow', 'Munich', 'Barcelona', 'Warsaw', 'Budapest', 'Stockholm', 'Riga', 'Edinburgh', 'Vienna']
    durations = {
        'Bucharest': 2,
        'Krakow': 4,
        'Munich': 3,
        'Barcelona': 5,
        'Warsaw': 5,
        'Budapest': 5,
        'Stockholm': 2,
        'Riga': 5,
        'Edinburgh': 5,
        'Vienna': 5
    }
    
    flight_str = "Budapest and Munich, Bucharest and Riga, Munich and Krakow, Munich and Warsaw, Munich and Bucharest, Edinburgh and Stockholm, Barcelona and Warsaw, Edinburgh and Krakow, Barcelona and Munich, Stockholm and Krakow, Budapest and Vienna, Barcelona and Stockholm, Stockholm and Munich, Edinburgh and Budapest, Barcelona and Riga, Edinburgh and Barcelona, Vienna and Riga, Barcelona and Budapest, Bucharest and Warsaw, Vienna and Krakow, Edinburgh and Munich, Barcelona and Bucharest, Edinburgh and Riga, Vienna and Stockholm, Warsaw and Krakow, Barcelona and Krakow, from Riga to Munich, Vienna and Bucharest, Budapest and Warsaw, Vienna and Warsaw, Barcelona and Vienna, Budapest and Bucharest, Vienna and Munich, Riga and Warsaw, Stockholm and Riga, Stockholm and Warsaw"
    flight_str = flight_str.replace("from ", "").replace(" to ", " and ")
    flights = flight_str.split(", ")
    direct_flights = set()
    for flight in flights:
        parts = flight.split(" and ")
        if len(parts) == 2:
            A, B = parts
            direct_flights.add((A, B))
            direct_flights.add((B, A))
    
    s = Solver()
    in_city = {city: [Bool(f"in_{city}_{day}") for day in range(1, 33)} for city in cities}
    
    for day in range(32):
        day_vars = [in_city[city][day] for city in cities]
        total_cities = Sum([If(v, 1, 0) for v in day_vars])
        option1 = (total_cities == 1)
        option2 = (total_cities == 2)
        constraints_for_option2 = []
        for i in range(len(cities)):
            for j in range(i+1, len(cities)):
                A = cities[i]
                B = cities[j]
                if (A, B) not in direct_flights and (B, A) not in direct_flights:
                    constraints_for_option2.append(Not(And(in_city[A][day], in_city[B][day])))
        s.add(Or(option1, And(option2, And(constraints_for_option2))))
    
    for day in range(31):
        common = Or([And(in_city[city][day], in_city[city][day+1]) for city in cities])
        s.add(common)
    
    for city in cities:
        total_days = Sum([If(in_city[city][day], 1, 0) for day in range(32)])
        s.add(total_days == durations[city])
    
    for day in [8, 9, 10, 11, 12]:
        s.add(in_city['Budapest'][day])
    for day in [24, 25, 26, 27, 28]:
        s.add(in_city['Warsaw'][day])
    for day in [17, 18, 19]:
        s.add(in_city['Munich'][day])
    s.add(Or(in_city['Stockholm'][16], in_city['Stockholm'][17]))
    s.add(Or([in_city['Edinburgh'][i] for i in range(5)]))
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for day in range(32):
            present_cities = []
            for city in cities:
                if m.evaluate(in_city[city][day]):
                    present_cities.append(city)
            if len(present_cities) == 1:
                place = present_cities[0]
            else:
                present_cities.sort()
                place = present_cities
            itinerary.append({"day": day+1, "place": place})
        
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()