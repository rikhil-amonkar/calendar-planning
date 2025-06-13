from z3 import *

def main():
    # Define the City enum
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
    
    # Required days for each city
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
    
    # Given flight connections (as string pairs)
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
    
    # Convert string pairs to City enum pairs (both directions)
    flight_pairs_const = []
    for a, b in given_flight_list:
        c1 = city_dict[a]
        c2 = city_dict[b]
        flight_pairs_const.append((c1, c2))
        flight_pairs_const.append((c2, c1))
    
    # Create Z3 variables for each day: start_i and end_i for i in 0..22 (representing days 1 to 23)
    num_days = 23
    start = [Const(f'start_{i}', City) for i in range(num_days)]
    end = [Const(f'end_{i}', City) for i in range(num_days)]
    
    s = Solver()
    
    # Constraint 1: Chain constraint: end_i == start_{i+1}
    for i in range(num_days - 1):
        s.add(end[i] == start[i+1])
    
    # Constraint 2: Travel constraint: if start_i != end_i, then (start_i, end_i) must be in flight_pairs_const
    for i in range(num_days):
        cond = Or([And(start[i] == a, end[i] == b) for (a, b) in flight_pairs_const])
        s.add(If(start[i] != end[i], cond, True))
    
    # Constraint 3: City duration constraints
    for city in [Rome, Mykonos, Lisbon, Frankfurt, Nice, Stuttgart, Venice, Dublin, Bucharest, Seville]:
        total = 0
        for i in range(num_days):
            # Count if start_i is the city
            total += If(start[i] == city, 1, 0)
            # Count if end_i is the city and start_i is not the same (i.e., travel day arriving in city)
            total += If(And(end[i] == city, start[i] != city), 1, 0)
        s.add(total == required_days[city])
    
    # Constraint 4: Fixed events
    # Mykonos on day 10 and 11 (indices 9 and 10)
    s.add(Or(start[9] == Mykonos, end[9] == Mykonos))
    s.add(Or(start[10] == Mykonos, end[10] == Mykonos))
    
    # Seville conference from day 13 to 17 (indices 12 to 16)
    for i in range(12, 17):  # days 13 to 17 (0-indexed: 12,13,14,15,16)
        s.add(Or(start[i] == Seville, end[i] == Seville))
    
    # Frankfurt wedding between day 1 and 5 (indices 0 to 4)
    s.add(Or([Or(start[i] == Frankfurt, end[i] == Frankfurt) for i in range(0, 5)]))
    
    # Forbid the previous invalid solution
    s.add(Not(And(
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
    )))
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        # Helper to convert enum to string
        def city_str(city_val):
            for name, c in city_dict.items():
                if m.evaluate(c) == city_val:
                    return name
            return "Unknown"
        
        # Print the plan
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