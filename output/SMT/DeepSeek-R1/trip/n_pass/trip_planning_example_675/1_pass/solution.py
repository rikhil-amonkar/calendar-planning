from z3 import *

def main():
    cities = ["Dubrovnik", "Split", "Milan", "Porto", "Krakow", "Munich"]
    days_req = {
        "Dubrovnik": 4,
        "Split": 3,
        "Milan": 3,
        "Porto": 4,
        "Krakow": 2,
        "Munich": 5
    }
    
    flights_set = {
        ("Munich", "Porto"),
        ("Split", "Milan"),
        ("Milan", "Porto"),
        ("Munich", "Krakow"),
        ("Munich", "Milan"),
        ("Dubrovnik", "Munich"),
        ("Krakow", "Split"),
        ("Krakow", "Milan"),
        ("Munich", "Split")
    }
    
    start = {c: Int(f'start_{c}') for c in cities}
    end = {c: Int(f'end_{c}') for c in cities}
    
    s = Solver()
    
    for c in cities:
        s.add(start[c] >= 1, start[c] <= 16)
        s.add(end[c] >= 1, end[c] <= 16)
        s.add(end[c] - start[c] + 1 == days_req[c])
    
    s.add(start["Munich"] == 4, end["Munich"] == 8)
    s.add(start["Krakow"] == 8, end["Krakow"] == 9)
    s.add(start["Milan"] == 11, end["Milan"] == 13)
    
    s.add(Distinct([start[c] for c in cities]))
    allowed_starts = [1, 4, 8, 9, 11, 13]
    for c in cities:
        s.add(Or([start[c] == d for d in allowed_starts]))
    
    days_sorted = sorted(allowed_starts)
    for i in range(5):
        d1 = days_sorted[i]
        d2 = days_sorted[i+1]
        constraints = []
        for c1 in cities:
            for c2 in cities:
                if c1 == c2:
                    continue
                in_flights = Or(
                    (c1, c2) in flights_set,
                    (c2, c1) in flights_set
                )
                constraints.append(And(start[c1] == d1, start[c2] == d2, in_flights))
        s.add(Or(constraints))
    
    if s.check() == sat:
        model = s.model()
        start_vals = {}
        end_vals = {}
        for c in cities:
            start_vals[c] = model.eval(start[c]).as_long()
            end_vals[c] = model.eval(end[c]).as_long()
        
        sorted_cities = sorted(cities, key=lambda c: start_vals[c])
        itinerary = []
        for idx, city in enumerate(sorted_cities):
            s_val = start_vals[city]
            e_val = end_vals[city]
            if s_val == e_val:
                day_str = f"Day {s_val}"
            else:
                day_str = f"Day {s_val}-{e_val}"
            itinerary.append({"day_range": day_str, "place": city})
            
            if idx < len(sorted_cities) - 1:
                itinerary.append({"day_range": f"Day {e_val}", "place": city})
                next_city = sorted_cities[idx+1]
                itinerary.append({"day_range": f"Day {e_val}", "place": next_city})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()