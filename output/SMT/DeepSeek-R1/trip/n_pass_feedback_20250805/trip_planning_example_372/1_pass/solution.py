import z3
import json

def main():
    n_days = 13
    cities = {"Madrid": 0, "Porto": 1, "Seville": 2, "Stuttgart": 3}
    inv_cities = {v: k for k, v in cities.items()}
    
    s = z3.Solver()
    
    start = [z3.Int(f'start_{i}') for i in range(n_days)]
    flight = [z3.Bool(f'flight_{i}') for i in range(n_days)]
    end = [z3.Int(f'end_{i}') for i in range(n_days)]
    
    for i in range(n_days):
        s.add(z3.Or([start[i] == 0, start[i] == 1, start[i] == 2, start[i] == 3]))
        s.add(z3.Or([end[i] == 0, end[i] == 1, end[i] == 2, end[i] == 3]))
        
        s.add(z3.Implies(flight[i], start[i] != end[i]))
        s.add(z3.Implies(flight[i], z3.Or(
            z3.And(start[i] == 1, end[i] == 3), z3.And(start[i] == 3, end[i] == 1),
            z3.And(start[i] == 2, end[i] == 1), z3.And(start[i] == 1, end[i] == 2),
            z3.And(start[i] == 0, end[i] == 1), z3.And(start[i] == 1, end[i] == 0),
            z3.And(start[i] == 0, end[i] == 2), z3.And(start[i] == 2, end[i] == 0)
        )))
        s.add(z3.Implies(z3.Not(flight[i]), end[i] == start[i]))
    
    for i in range(1, n_days):
        s.add(start[i] == end[i-1])
    
    s.add(z3.Sum([z3.If(flight[i], 1, 0) for i in range(n_days)]) == 3)
    
    total_days = [0]*4
    for c in range(4):
        count_start = z3.Sum([z3.If(start[i] == c, 1, 0) for i in range(n_days)])
        count_end_flight = z3.Sum([z3.If(z3.And(flight[i], end[i] == c), 1, 0) for i in range(n_days)])
        total_days[c] = count_start + count_end_flight
    s.add(total_days[0] == 4)
    s.add(total_days[1] == 3)
    s.add(total_days[2] == 2)
    s.add(total_days[3] == 7)
    
    s.add(z3.Or(start[6] == 3, z3.And(flight[6], end[6] == 3)))
    s.add(z3.Or(start[12] == 3, z3.And(flight[12], end[12] == 3)))
    
    s.add(z3.Or(
        z3.Or(start[0] == 0, z3.And(flight[0], end[0] == 0)),
        z3.Or(start[1] == 0, z3.And(flight[1], end[1] == 0)),
        z3.Or(start[2] == 0, z3.And(flight[2], end[2] == 0)),
        z3.Or(start[3] == 0, z3.And(flight[3], end[3] == 0))
    ))
    
    if s.check() == z3.sat:
        m = s.model()
        start_vals = [m.evaluate(start[i]) for i in range(n_days)]
        flight_vals = [m.evaluate(flight[i]) for i in range(n_days)]
        end_vals = [m.evaluate(end[i]) for i in range(n_days)]
        
        itinerary = []
        for i in range(n_days):
            day = i + 1
            places = [inv_cities[int(str(start_vals[i]))]]
            if z3.is_true(flight_vals[i]):
                end_city_val = int(str(end_vals[i]))
                places.append(inv_cities[end_city_val])
            itinerary.append({"day": day, "place": places})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()