import z3
import json

def main():
    City = z3.Datatype('City')
    City.declare('Santorini')
    City.declare('Krakow')
    City.declare('Paris')
    City.declare('Vilnius')
    City.declare('Munich')
    City.declare('Geneva')
    City.declare('Amsterdam')
    City.declare('Budapest')
    City.declare('Split')
    City = City.create()
    
    Santorini = City.Santorini
    Krakow = City.Krakow
    Paris = City.Paris
    Vilnius = City.Vilnius
    Munich = City.Munich
    Geneva = City.Geneva
    Amsterdam = City.Amsterdam
    Budapest = City.Budapest
    Split = City.Split
    
    cities = [Santorini, Krakow, Paris, Vilnius, Munich, Geneva, Amsterdam, Budapest, Split]
    
    directed_edges = set()
    directed_edges.add((Vilnius, Munich))
    directed_edges.add((Krakow, Vilnius))
    
    undirected_pairs = [
        (Paris, Krakow), (Paris, Amsterdam), (Paris, Split), (Paris, Geneva),
        (Amsterdam, Geneva), (Munich, Split), (Split, Krakow), (Munich, Amsterdam),
        (Budapest, Amsterdam), (Split, Geneva), (Vilnius, Split), (Munich, Geneva),
        (Munich, Krakow), (Vilnius, Amsterdam), (Budapest, Paris), (Krakow, Amsterdam),
        (Vilnius, Paris), (Budapest, Geneva), (Split, Amsterdam), (Santorini, Geneva),
        (Amsterdam, Santorini), (Munich, Budapest), (Munich, Paris)
    ]
    
    for a, b in undirected_pairs:
        directed_edges.add((a, b))
        directed_edges.add((b, a))
    
    C = [z3.Const(f'C_{i}', City) for i in range(31)]
    
    s = z3.Solver()
    
    s.add(C[0] == Vilnius)
    s.add(C[30] == Vilnius)
    
    for i in range(1, 31):
        start_city = C[i-1]
        end_city = C[i]
        flight_possible = z3.Or([z3.And(start_city == a, end_city == b) for (a, b) in directed_edges])
        s.add(z3.If(start_city != end_city, flight_possible, True))
    
    city_days = {
        Santorini: 5,
        Krakow: 5,
        Paris: 5,
        Vilnius: 3,
        Munich: 5,
        Geneva: 2,
        Amsterdam: 4,
        Budapest: 5,
        Split: 4
    }
    
    for city, total in city_days.items():
        total_days = z3.Sum([z3.If(z3.Or(C[i-1] == city, C[i] == city), 1, 0) for i in range(1, 31)])
        s.add(total_days == total)
    
    santorini_in_window = z3.Or([z3.Or(C[i-1] == Santorini, C[i] == Santorini) for i in range(25, 30)])
    s.add(santorini_in_window)
    
    krakow_in_window = z3.Or([z3.Or(C[i-1] == Krakow, C[i] == Krakow) for i in range(18, 23)])
    s.add(krakow_in_window)
    
    paris_in_window = z3.Or([z3.Or(C[i-1] == Paris, C[i] == Paris) for i in range(11, 16)])
    s.add(paris_in_window)
    
    if s.check() == z3.sat:
        model = s.model()
        itinerary = []
        for day in range(1, 31):
            start = model.eval(C[day-1])
            end = model.eval(C[day])
            if start.eq(end):
                itinerary.append({"day": day, "cities": [str(start)]})
            else:
                itinerary.append({"day": day, "cities": [str(start), str(end)]})
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()