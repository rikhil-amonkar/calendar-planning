import z3
import json

def main():
    # Define the City enum
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
    
    # City constants
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
    
    # Build the directed flight graph
    directed_edges = set()
    directed_edges.add((Vilnius, Munich))
    directed_edges.add((Krakow, Vilnius))
    
    undirected_pairs = [
        (Paris, Krakow),
        (Paris, Amsterdam),
        (Paris, Split),
        (Paris, Geneva),
        (Amsterdam, Geneva),
        (Munich, Split),
        (Split, Krakow),
        (Munich, Amsterdam),
        (Budapest, Amsterdam),
        (Split, Geneva),
        (Vilnius, Split),
        (Munich, Geneva),
        (Munich, Krakow),
        (Vilnius, Amsterdam),
        (Budapest, Paris),
        (Krakow, Amsterdam),
        (Vilnius, Paris),
        (Budapest, Geneva),
        (Split, Amsterdam),
        (Santorini, Geneva),
        (Amsterdam, Santorini),
        (Munich, Budapest),
        (Munich, Paris)
    ]
    
    for (a, b) in undirected_pairs:
        directed_edges.add((a, b))
        directed_edges.add((b, a))
    
    # Create variables: C0 (start of day1) and C1 to C30 (end of day1 to day30)
    C = [z3.Const(f'C_{i}', City) for i in range(0, 31)]  # C0 to C30
    
    s = z3.Solver()
    
    # Flight constraints for each day i (from 1 to 30): if the start city (C_{i-1}) != end city (C_i), then there must be a direct flight
    for i in range(1, 31):
        start_city = C[i-1]
        end_city = C[i]
        flight_possible = z3.Or([z3.And(start_city == a, end_city == b) for (a, b) in directed_edges])
        s.add(z3.If(start_city != end_city, flight_possible, True))
    
    # Total days per city: for a city c, total_days = number of days i (from 1 to 30) such that either C_{i-1}==c or C_i==c
    totals = {}
    for c in cities:
        total_days = 0
        for i in range(1, 31):
            in_city = z3.Or(C[i-1] == c, C[i] == c)
            total_days += z3.If(in_city, 1, 0)
        totals[c] = total_days
    
    s.add(totals[Santorini] == 5)
    s.add(totals[Krakow] == 5)
    s.add(totals[Paris] == 5)
    s.add(totals[Vilnius] == 3)
    s.add(totals[Munich] == 5)
    s.add(totals[Geneva] == 2)
    s.add(totals[Amsterdam] == 4)
    s.add(totals[Budapest] == 5)
    s.add(totals[Split] == 4)
    
    # Event constraints: at least one day in the specified ranges
    # Santorini between day 25 and 29 (inclusive) -> days 25,26,27,28,29
    santorini_days = []
    for day in range(25, 30):  # day from 25 to 29 inclusive
        i = day  # the day index in our 1..30 system
        # For day i, we use C[i-1] (morning) and C[i] (evening)
        santorini_days.append(z3.Or(C[i-1] == Santorini, C[i] == Santorini))
    s.add(z3.Or(santorini_days))
    
    # Krakow between day 18 and 22 (inclusive) -> days 18,19,20,21,22
    krakow_days = []
    for day in range(18, 23):  # 18 to 22 inclusive
        i = day
        krakow_days.append(z3.Or(C[i-1] == Krakow, C[i] == Krakow))
    s.add(z3.Or(krakow_days))
    
    # Paris between day 11 and 15 (inclusive) -> days 11,12,13,14,15
    paris_days = []
    for day in range(11, 16):  # 11 to 15 inclusive
        i = day
        paris_days.append(z3.Or(C[i-1] == Paris, C[i] == Paris))
    s.add(z3.Or(paris_days))
    
    # Solve the constraints
    if s.check() == z3.sat:
        model = s.model()
        itinerary_list = []
        for day in range(1, 31):
            start_city = model[C[day-1]]
            end_city = model[C[day]]
            if start_city.as_long() == end_city.as_long():
                cities_list = [str(start_city)]
            else:
                cities_list = [str(start_city), str(end_city)]
            itinerary_list.append({"day": day, "cities": cities_list})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()