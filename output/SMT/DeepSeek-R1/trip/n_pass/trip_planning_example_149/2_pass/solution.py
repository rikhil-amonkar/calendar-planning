from z3 import *

def main():
    cities = ["London", "Santorini", "Istanbul"]
    n_days = 10
    
    s = [Int(f's_{i}') for i in range(1, n_days+1)]
    e = [Int(f'e_{i}') for i in range(1, n_days+1)]
    
    solver = Solver()
    
    for i in range(n_days):
        solver.add(Or(s[i] == 0, s[i] == 1, s[i] == 2))
        solver.add(Or(e[i] == 0, e[i] == 1, e[i] == 2))
    
    for i in range(n_days-1):
        solver.add(e[i] == s[i+1])
    
    allowed_flights = [(0,1), (1,0), (0,2), (2,0)]
    for i in range(n_days):
        solver.add(If(s[i] != e[i], 
                     Or([And(s[i] == a, e[i] == b) for (a,b) in allowed_flights]),
                     True))
    
    solver.add(Or(s[4] == 1, e[4] == 1))
    solver.add(Or(s[9] == 1, e[9] == 1))
    
    london_days = 0
    santorini_days = 0
    istanbul_days = 0
    
    for i in range(n_days):
        london_days += If(Or(s[i] == 0, And(e[i] == 0, s[i] != 0)), 1, 0)
        santorini_days += If(Or(s[i] == 1, And(e[i] == 1, s[i] != 1)), 1, 0)
        istanbul_days += If(Or(s[i] == 2, And(e[i] == 2, s[i] != 2)), 1, 0)
    
    solver.add(london_days == 3)
    solver.add(santorini_days == 6)
    solver.add(istanbul_days == 3)
    
    if solver.check() == sat:
        model = solver.model()
        s_val = [model.evaluate(s_i).as_long() for s_i in s]
        e_val = [model.evaluate(e_i).as_long() for e_i in e]
        
        flight_days = []
        for i in range(n_days):
            if s_val[i] != e_val[i]:
                flight_days.append(i+1)
                
        if len(flight_days) < 2:
            extra_days = [d for d in [1,2,3,4,5,6,7,8,9,10] if d not in flight_days]
            while len(flight_days) < 2 and extra_days:
                flight_days.append(extra_days.pop(0))
            flight_days = sorted(flight_days[:2])
        else:
            flight_days = sorted(flight_days[:2])
        
        itinerary = []
        d1 = flight_days[0]
        if d1 > 1:
            start = 1
            end = d1 - 1
            city_idx = s_val[0]
            city_name = cities[city_idx]
            if start == end:
                itinerary.append({"day_range": f"Day {start}", "place": city_name})
            else:
                itinerary.append({"day_range": f"Day {start}-{end}", "place": city_name})
                
        dep_city1 = cities[s_val[d1-1]]
        arr_city1 = cities[e_val[d1-1]]
        itinerary.append({"day_range": f"Day {d1}", "place": dep_city1})
        itinerary.append({"day_range": f"Day {d1}", "place": arr_city1})
        
        d2 = flight_days[1]
        if d2 - d1 > 1:
            start = d1 + 1
            end = d2 - 1
            city_name = arr_city1
            if start == end:
                itinerary.append({"day_range": f"Day {start}", "place": city_name})
            else:
                itinerary.append({"day_range": f"Day {start}-{end}", "place": city_name})
                
        dep_city2 = cities[s_val[d2-1]]
        arr_city2 = cities[e_val[d2-1]]
        itinerary.append({"day_range": f"Day {d2}", "place": dep_city2})
        itinerary.append({"day_range": f"Day {d2}", "place": arr_city2})
        
        if d2 < n_days:
            start = d2 + 1
            end = n_days
            city_name = arr_city2
            if start == end:
                itinerary.append({"day_range": f"Day {start}", "place": city_name})
            else:
                itinerary.append({"day_range": f"Day {start}-{end}", "place": city_name})
                
        print({"itinerary": itinerary})
    else:
        print("No solution found")

if __name__ == "__main__":
    main()