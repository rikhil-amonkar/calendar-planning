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
        
        flight_days = [s_val[i] != e_val[i] for i in range(n_days)]
        
        segments = []
        current_segment = None
        
        for i in range(n_days):
            day_num = i + 1
            if flight_days[i]:
                dep_city = cities[s_val[i]]
                arr_city = cities[e_val[i]]
                if current_segment is not None and current_segment['place'] == dep_city:
                    current_segment['end'] = day_num
                else:
                    if current_segment is not None:
                        segments.append(current_segment)
                    current_segment = {'start': day_num, 'end': day_num, 'place': dep_city}
                segments.append(current_segment)
                current_segment = {'start': day_num, 'end': day_num, 'place': arr_city}
            else:
                city = cities[s_val[i]]
                if current_segment is not None and current_segment['place'] == city:
                    current_segment['end'] = day_num
                else:
                    if current_segment is not None:
                        segments.append(current_segment)
                    current_segment = {'start': day_num, 'end': day_num, 'place': city}
        
        if current_segment is not None:
            segments.append(current_segment)
        
        itinerary = []
        for seg in segments:
            start = seg['start']
            end = seg['end']
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({'day_range': day_range_str, 'place': seg['place']})
        
        print({"itinerary": itinerary})
    else:
        print("No solution found")

if __name__ == "__main__":
    main()