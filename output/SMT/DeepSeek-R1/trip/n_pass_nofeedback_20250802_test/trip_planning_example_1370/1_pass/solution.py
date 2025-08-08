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
    
    # Create morning and evening variables for each day (1 to 30)
    M = [z3.Const('M_%d' % i, City) for i in range(1, 31)]
    E = [z3.Const('E_%d' % i, City) for i in range(1, 31)]
    
    s = z3.Solver()
    
    # Constraint: Evening of day i is morning of day i+1 for i=1 to 29
    for i in range(0, 29):
        s.add(E[i] == M[i+1])
    
    # Flight constraints for each day
    for i in range(30):
        m_city = M[i]
        e_city = E[i]
        flight_possible = z3.Or([z3.And(m_city == a, e_city == b) for (a, b) in directed_edges])
        s.add(z3.If(m_city != e_city, flight_possible, True))
    
    # Total days per city
    totals = {}
    for c in cities:
        total_days = 0
        for i in range(30):
            in_city = z3.Or(M[i] == c, E[i] == c)
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
    # Santorini between day 25 and 29 (inclusive)
    santorini_days = []
    for day_index in [24, 25, 26, 27, 28]:
        in_city = z3.Or(M[day_index] == Santorini, E[day_index] == Santorini)
        santorini_days.append(in_city)
    s.add(z3.Or(santorini_days))
    
    # Krakow between day 18 and 22 (inclusive)
    krakow_days = []
    for day_index in [17, 18, 19, 20, 21]:
        in_city = z3.Or(M[day_index] == Krakow, E[day_index] == Krakow)
        krakow_days.append(in_city)
    s.add(z3.Or(krakow_days))
    
    # Paris between day 11 and 15 (inclusive)
    paris_days = []
    for day_index in [10, 11, 12, 13, 14]:
        in_city = z3.Or(M[day_index] == Paris, E[day_index] == Paris)
        paris_days.append(in_city)
    s.add(z3.Or(paris_days))
    
    # Solve the constraints
    if s.check() == z3.sat:
        model = s.model()
        itinerary_list = []
        for i in range(30):
            day_num = i + 1
            m_val = model[M[i]]
            e_val = model[E[i]]
            m_name = str(m_val)
            e_name = str(e_val)
            if m_name == e_name:
                cities_list = [m_name]
            else:
                cities_list = [m_name, e_name]
            itinerary_list.append({"day": day_num, "cities": cities_list})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()