from z3 import *

def main():
    s = Solver()
    
    cities = ["Dublin", "Krakow", "Istanbul", "Venice", "Naples", "Brussels", "Mykonos", "Frankfurt"]
    n_days = 21
    n_cities = 8
    
    c = [Int(f"c_{i}") for i in range(1, n_days+1)]
    for i in range(n_days):
        s.add(c[i] >= 0, c[i] < n_cities)
    
    city_to_idx = {
        "Dublin": 0,
        "Krakow": 1,
        "Istanbul": 2,
        "Venice": 3,
        "Naples": 4,
        "Brussels": 5,
        "Mykonos": 6,
        "Frankfurt": 7
    }

    bidirectional_pairs = [
        ("Dublin", "Brussels"),
        ("Mykonos", "Naples"),
        ("Venice", "Istanbul"),
        ("Frankfurt", "Krakow"),
        ("Naples", "Dublin"),
        ("Krakow", "Brussels"),
        ("Naples", "Istanbul"),
        ("Naples", "Brussels"),
        ("Istanbul", "Frankfurt"),
        ("Istanbul", "Krakow"),
        ("Istanbul", "Brussels"),
        ("Venice", "Frankfurt"),
        ("Naples", "Frankfurt"),
        ("Dublin", "Krakow"),
        ("Venice", "Brussels"),
        ("Naples", "Venice"),
        ("Istanbul", "Dublin"),
        ("Venice", "Dublin"),
        ("Dublin", "Frankfurt")
    ]
    
    directed_pairs = [
        ("Brussels", "Frankfurt")
    ]
    
    edges = []
    for a, b in bidirectional_pairs:
        a_idx = city_to_idx[a]
        b_idx = city_to_idx[b]
        edges.append((a_idx, b_idx))
        edges.append((b_idx, a_idx))
    for a, b in directed_pairs:
        a_idx = city_to_idx[a]
        b_idx = city_to_idx[b]
        edges.append((a_idx, b_idx))
    
    for i in range(n_days - 1):
        current_city = c[i]
        next_city = c[i+1]
        flight_taken = current_city != next_city
        valid_flight = Or([And(current_city == a, next_city == b) for (a, b) in edges])
        s.add(If(flight_taken, valid_flight, True))
    
    total_days_per_city = [0] * n_cities
    for city in range(n_cities):
        conditions = []
        for i in range(n_days):
            if i < n_days - 1:
                in_city_depart = c[i] == city
                flight_arrive = And(c[i] != city, c[i+1] == city)
                conditions.append(If(Or(in_city_depart, flight_arrive), 1, 0))
            else:
                conditions.append(If(c[i] == city, 1, 0))
        total_days_per_city[city] = Sum(conditions)
    
    s.add(total_days_per_city[0] == 5)   # Dublin
    s.add(total_days_per_city[1] == 4)   # Krakow
    s.add(total_days_per_city[2] == 3)   # Istanbul
    s.add(total_days_per_city[3] == 3)   # Venice
    s.add(total_days_per_city[4] == 4)   # Naples
    s.add(total_days_per_city[5] == 2)   # Brussels
    s.add(total_days_per_city[6] == 4)   # Mykonos
    s.add(total_days_per_city[7] == 3)   # Frankfurt
    
    dublin_days = [10, 11, 12, 13, 14]  # 1-indexed days 11 to 15 (0-indexed: 10 to 14)
    for d in dublin_days:
        if d < n_days - 1:
            s.add(Or(c[d] == 0, And(c[d] != 0, c[d+1] == 0)))
        else:
            s.add(c[d] == 0)
    
    mykonos_days = [0, 1, 2, 3]  # 1-indexed days 1 to 4 (0-indexed: 0 to 3)
    s.add(Or([Or(c[d] == 6, 
                 And(d < n_days-1, c[d] != 6, c[d+1] == 6)) for d in mykonos_days]))
    
    istanbul_days = [8, 9, 10]  # 1-indexed days 9,10,11 (0-indexed: 8,9,10)
    s.add(Or([Or(c[d] == 2, 
                 And(d < n_days-1, c[d] != 2, c[d+1] == 2)) for d in istanbul_days]))
    
    frankfurt_days = [14, 15, 16]  # 1-indexed days 15,16,17 (0-indexed: 14,15,16)
    s.add(Or([Or(c[d] == 7, 
                 And(d < n_days-1, c[d] != 7, c[d+1] == 7)) for d in frankfurt_days]))
    
    if s.check() == sat:
        m = s.model()
        plan = [m.evaluate(c[i]).as_long() for i in range(n_days)]
        print("Day-by-day city schedule:")
        for day in range(1, n_days+1):
            city_index = plan[day-1]
            print(f"Day {day}: {cities[city_index]}")
        print("\nFlight days (when city changes):")
        for day in range(1, n_days):
            if plan[day-1] != plan[day]:
                print(f"Day {day}: Flight from {cities[plan[day-1]]} to {cities[plan[day]]}")
    else:
        print("No valid schedule found.")

if __name__ == "__main__":
    main()