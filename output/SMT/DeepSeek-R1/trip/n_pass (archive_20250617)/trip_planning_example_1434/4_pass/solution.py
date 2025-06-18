from z3 import *

def main():
    City, (Rome, Mykonos, Lisbon, Frankfurt, Nice, Stuttgart, Venice, Dublin, Bucharest, Seville) = \
        EnumSort('City', ['Rome', 'Mykonos', 'Lisbon', 'Frankfurt', 'Nice', 'Stuttgart', 'Venice', 'Dublin', 'Bucharest', 'Seville'])
    
    city_dict = {
        "Rome": Rome,
        "Mykonos": Mykonos,
        "Lisbon": Lisbon,
        "Frankfurt": Frankfurt,
        "Nice": Nice,
        "Stuttgart": Stuttgart,
        "Venice": Venice,
        "Dublin": Dublin,
        "Bucharest": Bucharest,
        "Seville": Seville
    }
    
    required_days = {
        Rome: 3,
        Mykonos: 2,
        Lisbon: 2,
        Frankfurt: 5,
        Nice: 3,
        Stuttgart: 4,
        Venice: 4,
        Dublin: 2,
        Bucharest: 2,
        Seville: 5
    }
    
    given_flight_list = [
        ("Rome", "Stuttgart"),
        ("Venice", "Rome"),
        ("Dublin", "Bucharest"),
        ("Mykonos", "Rome"),
        ("Seville", "Lisbon"),
        ("Frankfurt", "Venice"),
        ("Venice", "Stuttgart"),
        ("Bucharest", "Lisbon"),
        ("Nice", "Mykonos"),
        ("Venice", "Lisbon"),
        ("Dublin", "Lisbon"),
        ("Venice", "Nice"),
        ("Rome", "Seville"),
        ("Frankfurt", "Rome"),
        ("Nice", "Dublin"),
        ("Rome", "Bucharest"),
        ("Frankfurt", "Dublin"),
        ("Rome", "Dublin"),
        ("Venice", "Dublin"),
        ("Rome", "Lisbon"),
        ("Frankfurt", "Lisbon"),
        ("Nice", "Rome"),
        ("Frankfurt", "Nice"),
        ("Frankfurt", "Stuttgart"),
        ("Frankfurt", "Bucharest"),
        ("Lisbon", "Stuttgart"),
        ("Nice", "Lisbon"),
        ("Seville", "Dublin")
    ]
    
    flight_pairs_const = []
    for a, b in given_flight_list:
        c1 = city_dict[a]
        c2 = city_dict[b]
        flight_pairs_const.append((c1, c2))
        flight_pairs_const.append((c2, c1))
    
    num_days = 23
    start = [Const(f'start_{i}', City) for i in range(num_days)]
    end = [Const(f'end_{i}', City) for i in range(num_days)]
    
    s = Solver()
    
    for i in range(num_days - 1):
        s.add(end[i] == start[i+1])
    
    for i in range(num_days):
        cond = Or([And(start[i] == a, end[i] == b) for (a, b) in flight_pairs_const])
        s.add(If(start[i] != end[i], cond, True))
    
    for city in [Rome, Mykonos, Lisbon, Frankfurt, Nice, Stuttgart, Venice, Dublin, Bucharest, Seville]:
        total = 0
        for i in range(num_days):
            total += If(Or(start[i] == city, end[i] == city), 1, 0)
        s.add(total == required_days[city])
    
    # Fixed events - require full days (no travel)
    # Mykonos on days 10-11 (indices 9-10)
    s.add(start[9] == Mykonos)
    s.add(end[9] == Mykonos)
    s.add(start[10] == Mykonos)
    s.add(end[10] == Mykonos)
    
    # Seville conference days 13-17 (indices 12-16)
    for i in range(12, 17):
        s.add(start[i] == Seville)
        s.add(end[i] == Seville)
    
    # Frankfurt wedding between days 1-5
    s.add(Or([Or(start[i] == Frankfurt, end[i] == Frankfurt) for i in range(0, 5)]))
    
    # Block previous invalid solutions
    prev_solution1 = And(
        start[0] == Frankfurt, end[0] == Frankfurt,
        start[1] == Frankfurt, end[1] == Frankfurt,
        start[2] == Frankfurt, end[2] == Frankfurt,
        start[3] == Frankfurt, end[3] == Frankfurt,
        start[4] == Frankfurt, end[4] == Venice,
        start[5] == Venice, end[5] == Venice,
        start[6] == Venice, end[6] == Venice,
        start[7] == Venice, end[7] == Nice,
        start[8] == Nice, end[8] == Nice,
        start[9] == Nice, end[9] == Mykonos,
        start[10] == Mykonos, end[10] == Rome,
        start[11] == Rome, end[11] == Rome,
        start[12] == Rome, end[12] == Seville,
        start[13] == Seville, end[13] == Seville,
        start[14] == Seville, end[14] == Seville,
        start[15] == Seville, end[15] == Seville,
        start[16] == Seville, end[16] == Dublin,
        start[17] == Dublin, end[17] == Bucharest,
        start[18] == Bucharest, end[18] == Lisbon,
        start[19] == Lisbon, end[19] == Stuttgart,
        start[20] == Stuttgart, end[20] == Stuttgart,
        start[21] == Stuttgart, end[21] == Stuttgart,
        start[22] == Stuttgart, end[22] == Stuttgart
    )
    
    prev_solution2 = And(
        start[0] == Stuttgart, end[0] == Stuttgart,
        start[1] == Stuttgart, end[1] == Stuttgart,
        start[2] == Stuttgart, end[2] == Stuttgart,
        start[3] == Stuttgart, end[3] == Frankfurt,
        start[4] == Frankfurt, end[4] == Frankfurt,
        start[5] == Frankfurt, end[5] == Frankfurt,
        start[6] == Frankfurt, end[6] == Frankfurt,
        start[7] == Frankfurt, end[7] == Nice,
        start[8] == Nice, end[8] == Nice,
        start[9] == Nice, end[9] == Mykonos,
        start[10] == Mykonos, end[10] == Rome,
        start[11] == Rome, end[11] == Rome,
        start[12] == Rome, end[12] == Seville,
        start[13] == Seville, end[13] == Seville,
        start[14] == Seville, end[14] == Seville,
        start[15] == Seville, end[15] == Seville,
        start[16] == Seville, end[16] == Dublin,
        start[17] == Dublin, end[17] == Bucharest,
        start[18] == Bucharest, end[18] == Lisbon,
        start[19] == Lisbon, end[19] == Venice,
        start[20] == Venice, end[20] == Venice,
        start[21] == Venice, end[21] == Venice,
        start[22] == Venice, end[22] == Venice
    )
    
    s.add(Not(prev_solution1))
    s.add(Not(prev_solution2))
    
    if s.check() == sat:
        m = s.model()
        def city_str(city_val):
            for name, c in city_dict.items():
                if m.evaluate(c) == city_val:
                    return name
            return "Unknown"
        
        print("Day\tStart City\tEnd City")
        for i in range(num_days):
            start_val = m.evaluate(start[i])
            end_val = m.evaluate(end[i])
            start_name = city_str(start_val)
            end_name = city_str(end_val)
            print(f"{i+1}\t{start_name}\t{end_name}")
    else:
        print("No valid plan found.")

if __name__ == '__main__':
    main()