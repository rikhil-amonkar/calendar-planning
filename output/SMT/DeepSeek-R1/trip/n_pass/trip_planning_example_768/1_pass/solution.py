from z3 import *

def main():
    s = Solver()
    
    cities = ["Mykonos", "Nice", "London", "Copenhagen", "Oslo", "Tallinn"]
    n_cities = len(cities)
    n_days = 16
    
    city = [Int(f'city_{i}') for i in range(n_days)]
    for i in range(n_days):
        s.add(city[i] >= 0, city[i] < n_cities)
    
    allowed_edges = [
        (0, 2), (2, 0),  # Mykonos-London
        (0, 1), (1, 0),  # Mykonos-Nice
        (2, 1), (1, 2),  # London-Nice
        (2, 3), (3, 2),  # London-Copenhagen
        (2, 4), (4, 2),  # London-Oslo
        (3, 5), (5, 3),  # Copenhagen-Tallinn
        (3, 1), (1, 3),  # Copenhagen-Nice
        (3, 4), (4, 3),  # Copenhagen-Oslo
        (4, 5), (5, 4),  # Oslo-Tallinn
        (4, 1), (1, 4)   # Oslo-Nice
    ]
    
    for i in range(1, n_days):
        same_city = (city[i-1] == city[i])
        flight_ok = Or([And(city[i-1] == a, city[i] == b) for (a, b) in allowed_edges])
        s.add(Or(same_city, flight_ok))
    
    total_days = [0] * n_cities
    for c in range(n_cities):
        total = 0
        conds = []
        conds.append(city[0] == c)
        for i in range(1, n_days):
            conds.append(Or(city[i-1] == c, city[i] == c))
        total_days[c] = Sum([If(cond, 1, 0) for cond in conds])
    
    s.add(total_days[0] == 4)  # Mykonos
    s.add(total_days[1] == 3)  # Nice
    s.add(total_days[2] == 2)  # London
    s.add(total_days[3] == 3)  # Copenhagen
    s.add(total_days[4] == 5)  # Oslo
    s.add(total_days[5] == 4)  # Tallinn
    
    s.add(Or(city[13] == 1, city[12] == 1))  # Nice on day14
    s.add(Or(city[15] == 1, city[14] == 1))  # Nice on day16
    
    oslo_conds = []
    for i in range(9, 14):
        oslo_conds.append(Or(city[i] == 4, city[i-1] == 4))
    s.add(Or(oslo_conds))
    
    if s.check() == sat:
        m = s.model()
        plan = [m.evaluate(city[i]).as_long() for i in range(n_days)]
        for day in range(n_days):
            city_name = cities[plan[day]]
            if day == 0:
                print(f"Day {day+1}: stay in {city_name}")
            else:
                prev_city = cities[plan[day-1]]
                if plan[day] == plan[day-1]:
                    print(f"Day {day+1}: stay in {city_name}")
                else:
                    print(f"Day {day+1}: fly from {prev_city} to {city_name}; therefore in {prev_city} and {city_name}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()