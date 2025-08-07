from z3 import *
import json

def main():
    cities = ["Brussels", "Helsinki", "Split", "Dubrovnik", "Istanbul", "Milan", "Vilnius", "Frankfurt"]
    
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
    
    directed_flights_set = set()
    for (a, b) in bidirectional_edges:
        i = cities.index(a)
        j = cities.index(b)
        directed_flights_set.add((i, j))
        directed_flights_set.add((j, i))
    for (a, b) in directed_edges:
        i = cities.index(a)
        j = cities.index(b)
        directed_flights_set.add((i, j))
    
    n_days = 22
    n_cities = len(cities)
    
    s = Solver()
    
    start_city = [Int(f'start_{d}') for d in range(n_days)]
    end_city = [Int(f'end_{d}') for d in range(n_days)]
    fly = [Bool(f'fly_{d}') for d in range(n_days)]
    in_city = [[Bool(f'in_{i}_{d}') for d in range(n_days)] for i in range(n_cities)]
    
    for d in range(n_days):
        s.add(start_city[d] >= 0, start_city[d] < n_cities)
        s.add(end_city[d] >= 0, end_city[d] < n_cities)
    
    s.add(start_city[0] == cities.index("Istanbul"))
    
    for d in range(1, n_days):
        s.add(start_city[d] == end_city[d-1])
    
    for d in range(n_days):
        s.add(If(fly[d], start_city[d] != end_city[d], start_city[d] == end_city[d]))
        allowed_flights = []
        for (i, j) in directed_flights_set:
            allowed_flights.append(And(start_city[d] == i, end_city[d] == j))
        s.add(Implies(fly[d], Or(allowed_flights)))
        
        for i in range(n_cities):
            s.add(in_city[i][d] == Or(start_city[d] == i, And(fly[d], end_city[d] == i)))
    
    for d in range(0, 5):
        s.add(in_city[cities.index("Istanbul")][d] == True)
    
    for d in [15, 16, 17]:
        s.add(in_city[cities.index("Frankfurt")][d] == True)
    
    for d in range(17, 22):
        s.add(in_city[cities.index("Vilnius")][d] == True)
    
    total_days = [0] * n_cities
    for i in range(n_cities):
        total_days[i] = Sum([If(in_city[i][d], 1, 0) for d in range(n_days)])
    s.add(total_days[cities.index("Brussels")] == 3)
    s.add(total_days[cities.index("Helsinki")] == 3)
    s.add(total_days[cities.index("Split")] == 4)
    s.add(total_days[cities.index("Dubrovnik")] == 2)
    s.add(total_days[cities.index("Istanbul")] == 5)
    s.add(total_days[cities.index("Milan")] == 4)
    s.add(total_days[cities.index("Vilnius")] == 5)
    s.add(total_days[cities.index("Frankfurt")] == 3)
    
    s.add(Sum([If(fly[d], 1, 0) for d in range(n_days)]) == 7)
    
    if s.check() == sat:
        m = s.model()
        itinerary = []
        for d in range(n_days):
            for i in range(n_cities):
                if m.evaluate(in_city[i][d]):
                    itinerary.append({"day": d+1, "place": cities[i]})
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()