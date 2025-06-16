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
    # Variables for each day: location at start and end of day, and travel flag
    start = [Const(f'start_{i}', CitySort) for i in range(n_days)]
    end = [Const(f'end_{i}', CitySort) for i in range(n_days)]
    travel = [Bool(f'travel_{i}') for i in range(n_days)]
    
    s = Solver()
    
    # Continuity between days
    for i in range(n_days - 1):
        s.add(end[i] == start[i+1])
    
    # Travel constraints
    for i in range(n_days):
        # If traveling, start and end different and connected by direct flight
        s.add(travel[i] == (start[i] != end[i]))
        s.add(Implies(travel[i], Or([And(start[i] == u, end[i] == v) for u, v in directed])))
    
    # Total days per city (including both cities on travel days)
    for city_name, days_req in cities.items():
        total_days = 0
        for i in range(n_days):
            # In city if: start there, or travel to there on that day
            in_city = Or(start[i] == c[city_name], 
                         And(travel[i], end[i] == c[city_name]))
            total_days += If(in_city, 1, 0)
        s.add(total_days == days_req)
    
    # Event constraints: must be in city during the specified days
    # Helper function to check if in a city on a given day
    def in_city(day, city):
        return Or(start[day] == city, 
                  And(travel[day], end[day] == city))
    
    # Brussels workshop between day 7-11 (0-indexed days 6 to 10)
    s.add(Or([in_city(i, c["Brussels"]) for i in range(6, 11)]))
    
    # Budapest meeting between day 16-17 (0-indexed days 15-16)
    s.add(Or([in_city(i, c["Budapest"]) for i in [15, 16]]))
    
    # Riga meeting between day 4-7 (0-indexed days 3-6)
    s.add(Or([in_city(i, c["Riga"]) for i in range(3, 7)]))
    
    # Solve and print itinerary
    if s.check() == sat:
        m = s.model()
        day_names = [str(i+1) for i in range(n_days)]
        print("Day\tStart\t\tTravel\tEnd\t\tCities Visited")
        for i in range(n_days):
            start_val = m.eval(start[i])
            end_val = m.eval(end[i])
            travel_val = m.eval(travel[i])
            start_city = [k for k,v in c.items() if eq(v, start_val)][0]
            end_city = [k for k,v in c.items() if eq(v, end_val)][0]
            travel_flag = is_true(travel_val)
            cities_visited = start_city
            if travel_flag:
                cities_visited += ", " + end_city
            print(f"{i+1}\t{start_city:<12}\t{travel_flag}\t{end_city:<12}\t{cities_visited}")
    else:
        print("No solution found")

def eq(a, b):
    return a.eq(b)

if __name__ == "__main__":
    main()