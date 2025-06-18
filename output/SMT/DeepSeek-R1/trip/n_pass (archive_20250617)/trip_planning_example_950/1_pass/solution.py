from z3 import *

def main():
    s = Solver()
    
    cities = ['Mykonos', 'Riga', 'Munich', 'Bucharest', 'Rome', 'Nice', 'Krakow']
    rev_city = {i: c for i, c in enumerate(cities)}
    
    allowed_flights = [
        (5,1), (1,5),   # Nice <-> Riga
        (3,2), (2,3),   # Bucharest <-> Munich
        (0,2), (2,0),   # Mykonos <-> Munich
        (1,3), (3,1),   # Riga <-> Bucharest
        (4,5), (5,4),   # Rome <-> Nice
        (4,2), (2,4),   # Rome <-> Munich
        (0,5), (5,0),   # Mykonos <-> Nice
        (4,0), (0,4),   # Rome <-> Mykonos
        (2,6), (6,2),   # Munich <-> Krakow
        (4,3), (3,4),   # Rome <-> Bucharest
        (5,2), (2,5),   # Nice <-> Munich
        (1,2),          # Riga -> Munich
        (4,1)           # Rome -> Riga
    ]
    
    num_days = 17
    num_cities = 7
    
    flight_taken = [Bool(f'flight_taken_{i}') for i in range(num_days)]
    start_city = [Int(f'start_city_{i}') for i in range(num_days)]
    end_city = [Int(f'end_city_{i}') for i in range(num_days)]
    from_city = [Int(f'from_city_{i}') for i in range(num_days)]
    to_city = [Int(f'to_city_{i}') for i in range(num_days)]
    
    in_city_d_c = []
    for d in range(num_days):
        in_day = []
        for c in range(num_cities):
            expr = If(flight_taken[d],
                      Or(start_city[d] == c, to_city[d] == c),
                      start_city[d] == c)
            in_day.append(expr)
        in_city_d_c.append(in_day)
    
    for d in range(num_days):
        s.add(start_city[d] >= 0, start_city[d] < num_cities)
        s.add(end_city[d] >= 0, end_city[d] < num_cities)
        s.add(from_city[d] >= 0, from_city[d] < num_cities)
        s.add(to_city[d] >= 0, to_city[d] < num_cities)
    
    s.add(start_city[0] == 4)  # Start in Rome (index 4) on day 1
    
    for d in range(1, num_days):
        s.add(start_city[d] == end_city[d-1])
    
    for d in range(num_days):
        allowed_here = []
        for flight in allowed_flights:
            i, j = flight
            allowed_here.append(And(from_city[d] == i, to_city[d] == j))
        flight_constraint = Or(allowed_here)
        
        s.add(If(flight_taken[d],
                 And(from_city[d] == start_city[d], flight_constraint, end_city[d] == to_city[d]),
                 end_city[d] == start_city[d]))
    
    total_flights = Sum([If(flight_taken[d], 1, 0) for d in range(num_days)])
    s.add(total_flights == 6)
    
    s.add(in_city_d_c[0][4] == True)  # In Rome on day 1
    s.add(in_city_d_c[3][4] == True)  # In Rome on day 4
    s.add(in_city_d_c[15][6] == True)  # In Krakow on day 16
    s.add(in_city_d_c[16][6] == True)  # In Krakow on day 17
    s.add(Or(in_city_d_c[3][0], in_city_d_c[4][0], in_city_d_c[5][0]))  # In Mykonos on day 4, 5, or 6
    
    total_days = [0] * num_cities
    for c in range(num_cities):
        total = 0
        for d in range(num_days):
            total += If(in_city_d_c[d][c], 1, 0)
        if c == 0:
            s.add(total == 3)  # Mykonos
        elif c == 1:
            s.add(total == 3)  # Riga
        elif c == 2:
            s.add(total == 4)  # Munich
        elif c == 3:
            s.add(total == 4)  # Bucharest
        elif c == 4:
            s.add(total == 4)  # Rome
        elif c == 5:
            s.add(total == 3)  # Nice
        elif c == 6:
            s.add(total == 2)  # Krakow
    
    if s.check() == sat:
        m = s.model()
        plan = []
        for d in range(num_days):
            ft_val = m.evaluate(flight_taken[d])
            sc_val = m.evaluate(start_city[d])
            ec_val = m.evaluate(end_city[d])
            sc_name = rev_city[int(str(sc_val))]
            ec_name = rev_city[int(str(ec_val))]
            if is_true(ft_val):
                fc_val = m.evaluate(from_city[d])
                tc_val = m.evaluate(to_city[d])
                fc_name = rev_city[int(str(fc_val))]
                tc_name = rev_city[int(str(tc_val))]
                plan.append(f"Day {d+1}: Fly from {fc_name} to {tc_name}")
            else:
                plan.append(f"Day {d+1}: Stay in {sc_name}")
        
        print("Trip Plan:")
        for p in plan:
            print(p)
        
        city_days = {city: 0 for city in cities}
        for d in range(num_days):
            for c in range(num_cities):
                if is_true(m.evaluate(in_city_d_c[d][c])):
                    city_days[rev_city[c]] += 1
        print("\nTotal days per city:")
        for city, days in city_days.items():
            print(f"{city}: {days} days")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()