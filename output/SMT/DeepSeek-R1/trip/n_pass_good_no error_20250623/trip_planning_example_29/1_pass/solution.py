import z3
import json

def main():
    s = z3.Solver()
    n_days = 10

    # City mapping: 0=Dubrovnik, 1=Frankfurt, 2=Krakow
    c = [z3.Int(f'c_{i}') for i in range(1, 12)]
    flight = [z3.Bool(f'flight_{i}') for i in range(1, 11)]
    
    # Each c[i] must be 0, 1, or 2
    for i in range(11):
        s.add(c[i] >= 0)
        s.add(c[i] <= 2)
    
    direct_flights = [(0, 1), (1, 0), (1, 2), (2, 1)]
    
    for i in range(10):
        flight_condition = z3.Or([z3.And(c[i] == a, c[i+1] == b) for (a, b) in direct_flights])
        s.add(z3.If(flight[i], flight_condition, c[i+1] == c[i]))
    
    s.add(z3.Sum([z3.If(flight[i], 1, 0) for i in range(10)]) == 2)
    
    k_count = 0
    d_count = 0
    f_count = 0
    for i in range(10):
        in_k_flight = z3.Or(c[i] == 2, c[i+1] == 2)
        in_k_non_flight = c[i] == 2
        k_count += z3.If(flight[i], z3.If(in_k_flight, 1, 0), z3.If(in_k_non_flight, 1, 0))
        
        in_d_flight = z3.Or(c[i] == 0, c[i+1] == 0)
        in_d_non_flight = c[i] == 0
        d_count += z3.If(flight[i], z3.If(in_d_flight, 1, 0), z3.If(in_d_non_flight, 1, 0))
        
        in_f_flight = z3.Or(c[i] == 1, c[i+1] == 1)
        in_f_non_flight = c[i] == 1
        f_count += z3.If(flight[i], z3.If(in_f_flight, 1, 0), z3.If(in_f_non_flight, 1, 0))
    
    s.add(k_count == 2)
    s.add(d_count == 7)
    s.add(f_count == 3)
    
    s.add(z3.If(flight[8], z3.Or(c[8] == 2, c[9] == 2), c[8] == 2))
    s.add(z3.If(flight[9], z3.Or(c[9] == 2, c[10] == 2), c[9] == 2))
    
    if s.check() == z3.sat:
        model = s.model()
        c_vals = [model.evaluate(c_i).as_long() for c_i in c]
        flight_vals = [z3.is_true(model.evaluate(flight_i)) for flight_i in flight]
        
        city_names = ["Dubrovnik", "Frankfurt", "Krakow"]
        start = 1
        current_city = c_vals[0]
        itinerary = []
        
        for i in range(10):
            day_num = i + 1
            if flight_vals[i]:
                if start <= day_num:
                    if start == day_num:
                        day_str = f"Day {day_num}"
                    else:
                        day_str = f"Day {start}-{day_num}"
                    itinerary.append({"day_range": day_str, "place": city_names[current_city]})
                
                itinerary.append({"day_range": f"Day {day_num}", "place": city_names[current_city]})
                next_city = c_vals[i+1]
                itinerary.append({"day_range": f"Day {day_num}", "place": city_names[next_city]})
                
                current_city = next_city
                start = day_num
                
        if start <= 10:
            if start == 10:
                day_str = "Day 10"
            else:
                day_str = f"Day {start}-10"
            itinerary.append({"day_range": day_str, "place": city_names[current_city]})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()