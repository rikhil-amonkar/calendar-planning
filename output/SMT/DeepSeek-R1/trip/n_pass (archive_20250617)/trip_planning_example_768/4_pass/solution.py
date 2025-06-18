from z3 import *

def main():
    s = Solver()
    
    cities = ["Mykonos", "Nice", "London", "Copenhagen", "Oslo", "Tallinn"]
    n_cities = len(cities)
    n_days = 16
    
    all_points = [Int(f'point_{i}') for i in range(-1, n_days)]
    s.add(all_points[-1] == 0)  # Start of day1 is Mykonos (index0)
    
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
    
    for i in range(0, n_days):
        a = all_points[i-1]
        b = all_points[i]
        stay = (a == b)
        fly = Or([And(a == edge_a, b == edge_b) for (edge_a, edge_b) in allowed_edges])
        s.add(Or(stay, fly))
    
    given_days = [4, 3, 2, 3, 5, 4]
    presence = []
    for c in range(n_cities):
        pres_c = []
        for j in range(0, n_days):
            in_city = Or(all_points[j-1] == c, all_points[j] == c)
            pres_c.append(in_city)
        presence.append(pres_c)
    
    for c in range(n_cities):
        total = Sum([If(presence[c][j], 1, 0) for j in range(n_days)])
        s.add(total == given_days[c])
    
    for c in range(n_cities):
        for start_j in range(0, n_days - 3):
            s.add(Not(And(
                presence[c][start_j],
                presence[c][start_j+1],
                presence[c][start_j+2],
                presence[c][start_j+3]
            )))
    
    s.add(Or([all_points[i] == 4 for i in range(8, 14)]))
    
    s.add(all_points[15] == 1)  # End in Nice on day16
    
    if s.check() == sat:
        m = s.model()
        points_val = [m.evaluate(all_points[i]) for i in range(-1, n_days)]
        for day in range(n_days):
            start_index = day - 1
            end_index = day
            start_city_val = points_val[start_index].as_long()
            end_city_val = points_val[end_index].as_long()
            if start_city_val == end_city_val:
                print(f"Day {day+1}: stay in {cities[start_city_val]}")
            else:
                print(f"Day {day+1}: fly from {cities[start_city_val]} to {cities[end_city_val]}; therefore in {cities[start_city_val]} and {cities[end_city_val]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()