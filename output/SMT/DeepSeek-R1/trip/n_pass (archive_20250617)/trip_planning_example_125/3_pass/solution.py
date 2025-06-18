from z3 import *

def main():
    CitySort, (stuttgart, seville, manchester) = EnumSort('City', ['stuttgart', 'seville', 'manchester'])
    city_map = {
        stuttgart: "Stuttgart",
        seville: "Seville",
        manchester: "Manchester"
    }
    
    s = Int('s')
    t = Int('t')
    city1 = Const('city1', CitySort)
    city2 = Const('city2', CitySort)
    city3 = Const('city3', CitySort)
    
    solver = Solver()
    
    solver.add(s >= 1, s < t, t <= 15)
    solver.add(Distinct(city1, city2, city3))
    
    # Direct flights: Manchester<->Seville, Stuttgart<->Manchester
    solver.add(Or(
        And(city1 == manchester, city2 == seville),
        And(city1 == seville, city2 == manchester),
        And(city1 == stuttgart, city2 == manchester),
        And(city1 == manchester, city2 == stuttgart)
    ))
    solver.add(Or(
        And(city2 == manchester, city3 == seville),
        And(city2 == seville, city3 == manchester),
        And(city2 == stuttgart, city3 == manchester),
        And(city2 == manchester, city3 == stuttgart)
    ))
    
    # Days per city calculation
    stuttgart_days = If(city1 == stuttgart, s,
                       If(city2 == stuttgart, t - s + 1,
                          16 - t))
    seville_days = If(city1 == seville, s,
                     If(city2 == seville, t - s + 1,
                        16 - t))
    manchester_days = If(city1 == manchester, s,
                        If(city2 == manchester, t - s + 1,
                            16 - t))
    
    solver.add(stuttgart_days == 6, seville_days == 7, manchester_days == 4)
    
    # Meeting constraint: non-travel day in Stuttgart between 1-6
    non_travel_stuttgart = []
    for d in range(1, 7):
        in_non_travel = Or(
            And(d < s, city1 == stuttgart),
            And(d > s, d < t, city2 == stuttgart),
            And(d > t, city3 == stuttgart)
        )
        non_travel_stuttgart.append(in_non_travel)
    solver.add(Or(non_travel_stuttgart))
    
    if solver.check() == sat:
        m = solver.model()
        s_val = m[s].as_long()
        t_val = m[t].as_long()
        city1_val = m[city1]
        city2_val = m[city2]
        city3_val = m[city3]
        
        for day in range(1, 16):
            if day < s_val:
                cities = [city_map[city1_val]]
            elif day == s_val:
                cities = [city_map[city1_val], city_map[city2_val]]
            elif day < t_val:
                cities = [city_map[city2_val]]
            elif day == t_val:
                cities = [city_map[city2_val], city_map[city3_val]]
            else:
                cities = [city_map[city3_val]]
            print(f"Day {day}: {', '.join(cities)}")
    else:
        print("No valid trip plan found.")

if __name__ == "__main__":
    main()