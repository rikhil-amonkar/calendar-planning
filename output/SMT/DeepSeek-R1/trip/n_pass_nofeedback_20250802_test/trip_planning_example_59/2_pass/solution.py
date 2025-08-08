import z3
import json

def main():
    days_total = 16
    stay = [z3.Int(f"stay_{i}") for i in range(days_total)]
    s = z3.Solver()
    
    for i in range(days_total):
        s.add(z3.Or(stay[i] == 0, stay[i] == 1, stay[i] == 2))
    
    for i in range(1, days_total):
        s.add(z3.Implies(stay[i-1] != stay[i],
                         z3.Or(
                             z3.And(stay[i-1] == 0, stay[i] == 1),
                             z3.And(stay[i-1] == 1, stay[i] == 0),
                             z3.And(stay[i-1] == 1, stay[i] == 2),
                             z3.And(stay[i-1] == 2, stay[i] == 1)
                         )))
    
    def presence(city, i):
        if i == 0:
            return stay[i] == city
        else:
            return z3.Or(stay[i] == city, z3.And(stay[i-1] == city, stay[i] != city))
    
    total_b = z3.Sum([z3.If(presence(0, i), 1, 0) for i in range(days_total)])
    total_l = z3.Sum([z3.If(presence(1, i), 1, 0) for i in range(days_total)])
    total_p = z3.Sum([z3.If(presence(2, i), 1, 0) for i in range(days_total)])
    
    s.add(total_b == 7)
    s.add(total_l == 7)
    s.add(total_p == 4)
    
    wedding_constraint = z3.Or([presence(0, i) for i in range(7)])
    s.add(wedding_constraint)
    
    if s.check() == z3.sat:
        m = s.model()
        stays_val = [m[stay[i]].as_long() for i in range(days_total)]
        
        city_days = {0: [], 1: [], 2: []}
        for i in range(days_total):
            for city in [0, 1, 2]:
                if i == 0:
                    if stays_val[i] == city:
                        city_days[city].append(i+1)
                else:
                    if stays_val[i] == city or (stays_val[i-1] == city and stays_val[i] != city):
                        city_days[city].append(i+1)
        
        segments = []
        city_names = {0: "Bucharest", 1: "Lyon", 2: "Porto"}
        for city in [0, 1, 2]:
            days_list = city_days[city]
            if not days_list:
                continue
            days_list.sort()
            start = days_list[0]
            end = days_list[0]
            groups = []
            for j in range(1, len(days_list)):
                if days_list[j] == days_list[j-1] + 1:
                    end = days_list[j]
                else:
                    groups.append((start, end))
                    start = days_list[j]
                    end = days_list[j]
            groups.append((start, end))
            
            for (s_start, s_end) in groups:
                if s_start == s_end:
                    day_range_str = f"Day {s_start}"
                else:
                    day_range_str = f"Day {s_start}-{s_end}"
                segments.append({'day_range': day_range_str, 'place': city_names[city]})
        
        segments.sort(key=lambda x: int(x['day_range'].split('-')[0].split()[1]))
        result = {'itinerary': segments}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()