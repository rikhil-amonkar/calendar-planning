from z3 import *

def main():
    s = [Int(f's_{i}') for i in range(5)]
    e = [Int(f'e_{i}') for i in range(5)]
    c = [String(f'c_{i}') for i in range(5)]
    
    solver = Solver()
    
    cities = ["Hamburg", "Munich", "Manchester", "Lyon", "Split"]
    
    solver.add(s[0] == 1)
    for i in range(4):
        solver.add(e[i] == s[i+1])
    solver.add(e[4] == 20)
    
    for i in range(5):
        solver.add(e[i] >= s[i])
    
    for i in range(5):
        solver.add(Or([c[i] == city for city in cities]))
    
    lyon_constraint = Or([And(c[i] == "Lyon", s[i] == 13, e[i] == 14) for i in range(5)])
    manchester_constraint = Or([And(c[i] == "Manchester", s[i] == 19, e[i] == 20) for i in range(5)])
    solver.add(lyon_constraint)
    solver.add(manchester_constraint)
    
    distinct_cities = Distinct(c)
    solver.add(distinct_cities)
    
    for i in range(5):
        length = e[i] - s[i] + 1
        solver.add(
            If(c[i] == "Hamburg", length == 7,
            If(c[i] == "Munich", length == 6,
            If(c[i] == "Manchester", length == 2,
            If(c[i] == "Lyon", length == 2,
            If(c[i] == "Split", length == 7, 
                length >= 1  # fallback, but cities are distinct and covered
            )))))
        )
    
    allowed_flights = [
        ("Split", "Munich"), ("Munich", "Split"),
        ("Munich", "Manchester"), ("Manchester", "Munich"),
        ("Hamburg", "Manchester"), ("Manchester", "Hamburg"),
        ("Hamburg", "Munich"), ("Munich", "Hamburg"),
        ("Split", "Lyon"), ("Lyon", "Split"),
        ("Lyon", "Munich"), ("Munich", "Lyon"),
        ("Hamburg", "Split"), ("Split", "Hamburg"),
        ("Manchester", "Split")
    ]
    
    for i in range(4):
        flight_allowed = Or([And(c[i] == f[0], c[i+1] == f[1]) for f in allowed_flights])
        solver.add(flight_allowed)
    
    if solver.check() == sat:
        model = solver.model()
        s_vals = [model.evaluate(s_i).as_long() for s_i in s]
        e_vals = [model.evaluate(e_i).as_long() for e_i in e]
        c_vals = [model.evaluate(c_i) for c_i in c]
        c_vals_str = [c_i.as_string() for c_i in c_vals]
        
        itinerary = []
        for i in range(5):
            start = s_vals[i]
            end = e_vals[i]
            city = c_vals_str[i]
            if start == end:
                day_str = f"Day {start}"
                itinerary.append({"day_range": day_str, "place": city})
            else:
                day_str = f"Day {start}-{end}"
                itinerary.append({"day_range": day_str, "place": city})
            if i < 4:
                flight_day = end
                itinerary.append({"day_range": f"Day {flight_day}", "place": city})
                itinerary.append({"day_range": f"Day {flight_day}", "place": c_vals_str[i+1]})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()