from z3 import *
import json

def main():
    cities = ["Brussels", "Helsinki", "Split", "Dubrovnik", "Istanbul", "Milan", "Vilnius", "Frankfurt"]
    n_cities = len(cities)
    n_days = 22
    
    Brussels_idx = cities.index("Brussels")
    Helsinki_idx = cities.index("Helsinki")
    Split_idx = cities.index("Split")
    Dubrovnik_idx = cities.index("Dubrovnik")
    Istanbul_idx = cities.index("Istanbul")
    Milan_idx = cities.index("Milan")
    Vilnius_idx = cities.index("Vilnius")
    Frankfurt_idx = cities.index("Frankfurt")
    
    bidirectional_edges = [
        ("Milan", "Frankfurt"),
        ("Split", "Frankfurt"),
        ("Milan", "Split"),
        ("Brussels", "Vilnius"),
        ("Brussels", "Helsinki"),
        ("Istanbul", "Brussels"),
        ("Milan", "Vilnius"),
        ("Brussels", "Milan"),
        ("Istanbul", "Helsinki"),
        ("Helsinki", "Vilnius"),
        ("Helsinki", "Dubrovnik"),
        ("Split", "Vilnius"),
        ("Istanbul", "Milan"),
        ("Helsinki", "Frankfurt"),
        ("Istanbul", "Vilnius"),
        ("Split", "Helsinki"),
        ("Milan", "Helsinki"),
        ("Istanbul", "Frankfurt"),
        ("Dubrovnik", "Frankfurt"),
        ("Frankfurt", "Vilnius")
    ]
    
    directed_edges = [
        ("Dubrovnik", "Istanbul"),
        ("Brussels", "Frankfurt")
    ]
    
    directed_flights = []
    for (a, b) in bidirectional_edges:
        i = cities.index(a)
        j = cities.index(b)
        directed_flights.append((i, j))
        directed_flights.append((j, i))
    for (a, b) in directed_edges:
        i = cities.index(a)
        j = cities.index(b)
        directed_flights.append((i, j))
    
    s = Solver()
    
    morning_city = [Int(f'morning_{d}') for d in range(n_days)]
    evening_city = [Int(f'evening_{d}') for d in range(n_days)]
    
    for d in range(n_days):
        s.add(morning_city[d] >= 0, morning_city[d] < n_cities)
        s.add(evening_city[d] >= 0, evening_city[d] < n_cities)
    
    s.add(morning_city[0] == Istanbul_idx)
    
    for d in range(1, n_days):
        s.add(morning_city[d] == evening_city[d-1])
    
    flight_day = [Bool(f'flight_{d}') for d in range(n_days)]
    for d in range(n_days):
        s.add(flight_day[d] == (morning_city[d] != evening_city[d]))
        valid_flight = Or([And(morning_city[d] == i, evening_city[d] == j) for (i, j) in directed_flights])
        s.add(Implies(flight_day[d], valid_flight))
    
    for d in range(4):
        s.add(morning_city[d] == Istanbul_idx)
        s.add(evening_city[d] == Istanbul_idx)
    
    s.add(morning_city[4] == Istanbul_idx)
    s.add(flight_day[4] == True)
    
    s.add(morning_city[15] == Frankfurt_idx, evening_city[15] == Frankfurt_idx)
    s.add(morning_city[16] == Frankfurt_idx, evening_city[16] == Frankfurt_idx)
    s.add(morning_city[17] == Frankfurt_idx)
    s.add(evening_city[17] == Vilnius_idx)
    
    for d in range(18, 22):
        s.add(morning_city[d] == Vilnius_idx)
        s.add(evening_city[d] == Vilnius_idx)
    
    total_days_per_city = [0] * n_cities
    for c in range(n_cities):
        total_days_per_city[c] = Sum([If(Or(morning_city[d] == c, evening_city[d] == c), 1, 0) for d in range(n_days)])
    
    s.add(total_days_per_city[Brussels_idx] == 3)
    s.add(total_days_per_city[Helsinki_idx] == 3)
    s.add(total_days_per_city[Split_idx] == 4)
    s.add(total_days_per_city[Dubrovnik_idx] == 2)
    s.add(total_days_per_city[Istanbul_idx] == 5)
    s.add(total_days_per_city[Milan_idx] == 4)
    s.add(total_days_per_city[Vilnius_idx] == 5)
    s.add(total_days_per_city[Frankfurt_idx] == 3)
    
    s.add(Sum([If(flight_day[d], 1, 0) for d in range(n_days)]) == 7)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in range(n_days):
            morn = m.eval(morning_city[d]).as_long()
            eve = m.eval(evening_city[d]).as_long()
            if morn == eve:
                itinerary.append({"day": d+1, "place": cities[morn]})
            else:
                itinerary.append({"day": d+1, "place": f"{cities[morn]} (morning) -> {cities[eve]} (evening)"})
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()