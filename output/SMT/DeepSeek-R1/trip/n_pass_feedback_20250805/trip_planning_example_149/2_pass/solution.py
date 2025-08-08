import z3
import json

def main():
    cities = ['Istanbul', 'London', 'Santorini']
    city = [z3.Int('city_%d' % i) for i in range(11)]
    s = z3.Solver()
    
    for i in range(11):
        s.add(z3.Or(city[i] == 0, city[i] == 1, city[i] == 2))
    
    for i in range(1, 11):
        s.add(z3.Or(
            city[i-1] == city[i],
            z3.And(city[i-1] == 0, city[i] == 1),
            z3.And(city[i-1] == 1, city[i] == 0),
            z3.And(city[i-1] == 1, city[i] == 2),
            z3.And(city[i-1] == 2, city[i] == 1)
        ))
    
    def count_days(c):
        return z3.Sum([z3.If(z3.Or(city[i-1] == c, city[i] == c), 1, 0) for i in range(1, 11)])
    
    s.add(count_days(0) == 3)  # Istanbul
    s.add(count_days(1) == 3)  # London
    s.add(count_days(2) == 6)  # Santorini
    
    s.add(z3.Or(city[4] == 2, city[5] == 2))  # Day 5: start or end in Santorini
    s.add(z3.Or(city[9] == 2, city[10] == 2)) # Day 10: start or end in Santorini
    
    if s.check() == z3.sat:
        m = s.model()
        city_vals = [m.evaluate(city[i]).as_long() for i in range(11)]
        
        stays = []
        start = 1
        current_city = city_vals[0]  # city at the beginning of day1 (end of day0)
        for i in range(1, 11):
            if city_vals[i] != current_city:
                stays.append((start, i, current_city))
                start = i
                current_city = city_vals[i]
        stays.append((start, 10, current_city))
        
        itinerary_list = []
        for (s_day, e_day, c_index) in stays:
            if s_day == e_day:
                day_range_str = f"Day {s_day}"
            else:
                day_range_str = f"Day {s_day}-{e_day}"
            itinerary_list.append({
                "day_range": day_range_str,
                "place": cities[c_index]
            })
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print('"unsat"')

if __name__ == '__main__':
    main()