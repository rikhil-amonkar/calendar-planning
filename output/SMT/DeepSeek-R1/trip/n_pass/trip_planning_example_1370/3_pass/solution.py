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
    
    # Build directed flight graph
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
    
    # Create city variables for each day (C0 to C30)
    C = [z3.Const(f'C_{i}', City) for i in range(31)]
    
    s = z3.Solver()
    s.set("sat.random_seed", 42)
    s.set("smt.random_seed", 42)
    
    # Fix starting city to Vilnius to break symmetry
    s.add(C[0] == Vilnius)
    
    # Flight constraints
    for i in range(1, 31):
        start_city = C[i-1]
        end_city = C[i]
        flight_possible = z3.Or([z3.And(start_city == a, end_city == b) for (a, b) in directed_edges])
        s.add(z3.If(start_city != end_city, flight_possible, True))
    
    # Total days per city using efficient Sum
    for c, total in zip(cities, [5, 5, 5, 3, 5, 2, 4, 5, 4]):
        total_days = z3.Sum([z3.If(z3.Or(C[i-1] == c, C[i] == c), 1, 0) for i in range(1, 31)])
        s.add(total_days == total)
    
    # Event windows with specific day assignments
    s.add(z3.Or(C[24] == Santorini, C[25] == Santorini))  # Day 25 or 26
    s.add(z3.Or(C[17] == Krakow, C[18] == Krakow))        # Day 18 or 19
    s.add(z3.Or(C[10] == Paris, C[11] == Paris))          # Day 11 or 12
    
    if s.check() == z3.sat:
        model = s.model()
        itinerary = []
        for day in range(1, 31):
            start = model[C[day-1]]
            end = model[C[day]]
            if start.eq(end):
                itinerary.append({"day": day, "cities": [str(start)]})
            else:
                itinerary.append({"day": day, "cities": [str(start), str(end)]})
        print(json.dumps({"itinerary": itinerary}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()