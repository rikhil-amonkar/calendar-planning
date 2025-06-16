from z3 import *

def main():
    # City names and required days
    cities = {
        "Brussels": 5,
        "Rome": 2,
        "Dubrovnik": 3,
        "Geneva": 5,
        "Budapest": 2,
        "Riga": 4,
        "Valencia": 2
    }
    city_names = list(cities.keys())
    CitySort, city_consts = EnumSort('City', city_names)
    c = dict(zip(city_names, city_consts))
    
    # Direct flights (bidirectional)
    direct_flights = [
        ("Brussels", "Valencia"),
        ("Rome", "Valencia"),
        ("Brussels", "Geneva"),
        ("Rome", "Geneva"),
        ("Dubrovnik", "Geneva"),
        ("Valencia", "Geneva"),
        ("Rome", "Riga"),
        ("Geneva", "Budapest"),
        ("Riga", "Brussels"),
        ("Rome", "Budapest"),
        ("Rome", "Brussels"),
        ("Brussels", "Budapest"),
        ("Dubrovnik", "Rome")
    ]
    # Create directed flights (both directions)
    directed = []
    for u, v in direct_flights:
        directed.append((c[u], c[v]))
        directed.append((c[v], c[u]))
    
    n_days = 17
    # Variables for each day
    start = [Const(f'start_{i}', CitySort) for i in range(n_days)]
    end = [Const(f'end_{i}', CitySort) for i in range(n_days)]
    travel = [Bool(f'travel_{i}') for i in range(n_days)]
    
    s = Solver()
    
    # Continuity between days
    for i in range(n_days - 1):
        s.add(end[i] == start[i+1])
    
    # Travel constraints
    for i in range(n_days):
        s.add(travel[i] == (start[i] != end[i]))
        s.add(Implies(travel[i], Or([And(start[i] == u, end[i] == v) for u, v in directed])))
    
    # Total days per city
    for city_name, days_req in cities.items():
        total_days = 0
        for i in range(n_days):
            in_city = Or(start[i] == c[city_name], 
                         And(travel[i], end[i] == c[city_name]))
            total_days += If(in_city, 1, 0)
        s.add(total_days == days_req)
    
    # Event constraints require full days (no travel)
    # Brussels workshop between day 7-11 (0-indexed days 6-10)
    s.add(Or([And(start[i] == c["Brussels"], Not(travel[i])) for i in range(6, 11)]))
    
    # Budapest meeting between day 16-17 (0-indexed days 15-16)
    s.add(Or([And(start[i] == c["Budapest"], Not(travel[i])) for i in [15, 16]]))
    
    # Riga meeting between day 4-7 (0-indexed days 3-6)
    s.add(Or([And(start[i] == c["Riga"], Not(travel[i])) for i in range(3, 7)]))
    
    # Solve
    if s.check() == sat:
        m = s.model()
        print("Day\tStart\t\tTravel\tEnd\t\tCities Visited")
        for i in range(n_days):
            start_val = m.eval(start[i])
            end_val = m.eval(end[i])
            travel_val = m.eval(travel[i])
            
            # Get city names
            start_city = [name for name, const in c.items() if m.eval(const) == start_val][0]
            end_city = [name for name, const in c.items() if m.eval(const) == end_val][0]
            
            travel_flag = is_true(travel_val)
            cities_visited = start_city
            if travel_flag:
                cities_visited += ", " + end_city
                
            print(f"{i+1}\t{start_city:<12}\t{travel_flag}\t{end_city:<12}\t{cities_visited}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()