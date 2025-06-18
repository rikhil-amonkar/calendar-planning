from z3 import *

def main():
    # Cities: Helsinki (0), Valencia (1), Dubrovnik (2), Porto (3), Prague (4), Reykjavik (5)
    given_edges = [(0, 4), (4, 1), (1, 3), (0, 5), (2, 0), (5, 4)]
    city_names = {0: 'Helsinki', 1: 'Valencia', 2: 'Dubrovnik', 3: 'Porto', 4: 'Prague', 5: 'Reykjavik'}

    s = Solver()
    city = [Int('city_%d' % d) for d in range(1, 19)]
    
    # Each day must be one of the cities
    for i in range(18):
        s.add(And(city[i] >= 0, city[i] <= 5))
    
    # Direct flight constraints for consecutive days
    for i in range(17):  # For consecutive pairs: (day1,day2), (day2,day3), ... (day17,day18)
        a = city[i]
        b = city[i+1]
        edge_conds = []
        for (u, v) in given_edges:
            edge_conds.append(And(a == u, b == v))
            edge_conds.append(And(a == v, b == u))
        s.add(Implies(a != b, Or(edge_conds)))
    
    # Total days per city (including travel days)
    def total_days(city_idx):
        total = 0
        for i in range(18):
            total += If(city[i] == city_idx, 1, 0)
        for i in range(1, 18):
            total += If(And(city[i] != city[i-1], city[i-1] == city_idx), 1, 0)
        return total
    
    s.add(total_days(0) == 4)  # Helsinki
    s.add(total_days(1) == 5)  # Valencia
    s.add(total_days(2) == 4)  # Dubrovnik
    s.add(total_days(3) == 3)  # Porto
    s.add(total_days(4) == 3)  # Prague
    s.add(total_days(5) == 4)  # Reykjavik
    
    # Porto meeting constraint (days 16, 17, or 18)
    porto_day16 = Or(city[15] == 3, And(city[15] != city[14], city[14] == 3))
    porto_day17 = Or(city[16] == 3, And(city[16] != city[15], city[15] == 3))
    porto_day18 = Or(city[17] == 3, And(city[17] != city[16], city[16] == 3))
    s.add(Or(porto_day16, porto_day17, porto_day18))
    
    # Solve and output
    if s.check() == sat:
        m = s.model()
        schedule = [m.evaluate(city[i]).as_long() for i in range(18)]
        for day in range(18):
            city_idx = schedule[day]
            city_name = city_names[city_idx]
            if day == 0:
                print(f"Day {day+1}: Stay in {city_name}")
            else:
                prev_city_idx = schedule[day-1]
                if city_idx == prev_city_idx:
                    print(f"Day {day+1}: Stay in {city_name}")
                else:
                    prev_city_name = city_names[prev_city_idx]
                    print(f"Day {day+1}: Travel from {prev_city_name} to {city_name}, so in both {prev_city_name} and {city_name}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()