from z3 import *

def main():
    s = Solver()
    
    cities = ["Dublin", "Krakow", "Istanbul", "Venice", "Naples", "Brussels", "Mykonos", "Frankfurt"]
    n_days = 21
    n_cities = 8
    
    c = [Int(f"c_{i}") for i in range(1, n_days+1)]
    for i in range(n_days):
        s.add(c[i] >= 0, c[i] < n_cities)
    
    edges = [
        (0, 5), (5, 0), (6, 4), (4, 6), (3, 2), (2, 3), (7, 1), (1, 7), (4, 0), (0, 4),
        (1, 5), (5, 1), (4, 2), (2, 4), (4, 5), (5, 4), (2, 7), (7, 2), (5, 7),
        (2, 1), (1, 2), (2, 5), (5, 2), (3, 7), (7, 3), (4, 7), (7, 4), (0, 1),
        (1, 0), (3, 5), (5, 3), (4, 3), (3, 4), (2, 0), (0, 2), (3, 0), (0, 3),
        (0, 7), (7, 0)
    ]
    
    for i in range(n_days - 1):
        current_city = c[i]
        next_city = c[i+1]
        flight_taken = current_city != next_city
        valid_flight = Or([And(current_city == a, next_city == b) for (a, b) in edges])
        s.add(If(flight_taken, valid_flight, True))
    
    total_days_per_city = [0] * n_cities
    for city in range(n_cities):
        conditions = []
        for i in range(n_days - 1):
            in_city_depart = c[i] == city
            flight_arrive = And(c[i] != c[i+1], c[i+1] == city)
            conditions.append(If(Or(in_city_depart, flight_arrive), 1, 0))
        conditions.append(If(c[n_days-1] == city, 1, 0))
        total_days_per_city[city] = Sum(conditions)
    
    s.add(total_days_per_city[0] == 5)
    s.add(total_days_per_city[1] == 4)
    s.add(total_days_per_city[2] == 3)
    s.add(total_days_per_city[3] == 3)
    s.add(total_days_per_city[4] == 4)
    s.add(total_days_per_city[5] == 2)
    s.add(total_days_per_city[6] == 4)
    s.add(total_days_per_city[7] == 3)
    
    dublin_days = [10, 11, 12, 13, 14]
    for d in dublin_days:
        in_dublin_depart = c[d] == 0
        flight_arrive_dublin = And(c[d] != c[d+1], c[d+1] == 0)
        s.add(Or(in_dublin_depart, flight_arrive_dublin))
    
    mykonos_days = []
    for d in [0, 1, 2, 3]:
        in_mykonos_depart = c[d] == 6
        flight_arrive_mykonos = And(c[d] != c[d+1], c[d+1] == 6)
        mykonos_days.append(Or(in_mykonos_depart, flight_arrive_mykonos))
    s.add(Or(mykonos_days))
    
    istanbul_days = []
    for d in [8, 9, 10]:
        in_istanbul_depart = c[d] == 2
        flight_arrive_istanbul = And(c[d] != c[d+1], c[d+1] == 2)
        istanbul_days.append(Or(in_istanbul_depart, flight_arrive_istanbul))
    s.add(Or(istanbul_days))
    
    frankfurt_days = []
    for d in [14, 15, 16]:
        in_frankfurt_depart = c[d] == 7
        flight_arrive_frankfurt = And(c[d] != c[d+1], c[d+1] == 7)
        frankfurt_days.append(Or(in_frankfurt_depart, flight_arrive_frankfurt))
    s.add(Or(frankfurt_days))
    
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