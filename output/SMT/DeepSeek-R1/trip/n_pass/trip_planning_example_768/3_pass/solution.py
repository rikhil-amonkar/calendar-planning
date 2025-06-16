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
    
    for i in range(n_days - 1):
        same_city = (city[i] == city[i+1])
        flight_ok = Or([And(city[i] == a, city[i+1] == b) for (a, b) in allowed_edges])
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
    
    s.add(Or(city[12] == 1, city[13] == 1))  # Nice on day14 (index13)
    s.add(city[15] == 1)  # Must end in Nice on day16 (index15)
    
    oslo_conds = []
    for j in range(9, 14):
        oslo_conds.append(Or(city[j-1] == 4, city[j] == 4))
    s.add(Or(oslo_conds))
    
    # Consecutive presence constraint
    for c in range(n_cities):
        for start in range(0, n_days - 3):
            consecutive = []
            for offset in range(4):
                day_index = start + offset
                if day_index == 0:
                    consecutive.append(city[0] == c)
                else:
                    consecutive.append(Or(city[day_index-1] == c, city[day_index] == c))
            s.add(Not(And(consecutive)))
    
    if s.check() == sat:
        m = s.model()
        plan = [m.evaluate(city[i]).as_long() for i in range(n_days)]
        for day in range(n_days):
            if day == 0:
                print(f"Day {day+1}: stay in {cities[plan[0]]}")
            else:
                prev_city_idx = plan[day-1]
                curr_city_idx = plan[day]
                if prev_city_idx == curr_city_idx:
                    print(f"Day {day+1}: stay in {cities[curr_city_idx]}")
                else:
                    print(f"Day {day+1}: fly from {cities[prev_city_idx]} to {cities[curr_city_idx]}; therefore in {cities[prev_city_idx]} and {cities[curr_city_idx]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()