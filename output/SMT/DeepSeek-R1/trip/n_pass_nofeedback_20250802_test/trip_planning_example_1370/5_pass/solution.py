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
    
    # Create city variables for each day (C0 to C30)
    C = [z3.Const(f'C_{i}', City) for i in range(31)]
    
    s = z3.Solver()
    s.set("sat.random_seed", 42)
    s.set("smt.random_seed", 42)
    
    # Define allowed flight function
    allowed = z3.Function('allowed', City, City, z3.BoolSort())
    for a in cities:
        for b in cities:
            if a == b or (a, b) in directed_edges:
                s.add(allowed(a, b) == True)
            else:
                s.add(allowed(a, b) == False)
    
    # Start and end in Vilnius
    s.add(C[0] == Vilnius)
    s.add(C[30] == Vilnius)
    
    # Flight constraints using the allowed function
    for i in range(1, 31):
        s.add(allowed(C[i-1], C[i]))
    
    # Total days per city using pseudo-boolean constraints
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
        # Create a list of booleans for each day indicating if city is visited
        in_city = [z3.Or(C[i-1] == city, C[i] == city) for i in range(1, 31)]
        # Use pseudo-boolean constraint for efficiency
        s.add(z3.PbEq([(cond, 1) for cond in in_city], total))
    
    # Event constraints
    santorini_days = [z3.Or(C[i-1] == Santorini, C[i] == Santorini) for i in range(25, 30)]
    s.add(z3.Or(santorini_days))
    
    krakow_days = [z3.Or(C[i-1] == Krakow, C[i] == Krakow) for i in range(18, 23)]
    s.add(z3.Or(krakow_days))
    
    paris_days = [z3.Or(C[i-1] == Paris, C[i] == Paris) for i in range(11, 16)]
    s.add(z3.Or(paris_days))
    
    # Solve the constraints
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