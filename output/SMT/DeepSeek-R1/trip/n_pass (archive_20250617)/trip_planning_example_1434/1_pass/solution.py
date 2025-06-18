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
    
    # Create Z3 variables for each day: city_start[d] and city_end[d] for d in 0..22 (representing days 1 to 23)
    num_days = 23
    city_start = [Const(f'city_start_{i+1}', City) for i in range(num_days)]
    city_end = [Const(f'city_end_{i+1}', City) for i in range(num_days)]
    
    s = Solver()
    
    # Constraint 1: Chain constraint: city_start of day i+1 equals city_end of day i
    for i in range(num_days - 1):
        s.add(city_start[i+1] == city_end[i])
    
    # Constraint 2: Travel constraint: if start != end on a day, then the pair must be in flight_pairs_const
    for i in range(num_days):
        start = city_start[i]
        end = city_end[i]
        travel_condition = Or([And(start == c1, end == c2) for (c1, c2) in flight_pairs_const])
        s.add(If(start != end, travel_condition, True))
    
    # Constraint 3: City duration constraints
    for city in [Rome, Mykonos, Lisbon, Frankfurt, Nice, Stuttgart, Venice, Dublin, Bucharest, Seville]:
        total = 0
        for i in range(num_days):
            # Count if city_start is the city
            total += If(city_start[i] == city, 1, 0)
            # Count if city_end is the city and city_start is not (to avoid double-counting when staying)
            total += If(And(city_end[i] == city, city_start[i] != city), 1, 0)
        s.add(total == required_days[city])
    
    # Constraint 4: Fixed events
    # Mykonos must be visited on day 10 and 11 (days at index 9 and 10)
    s.add(Or(city_start[9] == Mykonos, city_end[9] == Mykonos))
    s.add(Or(city_start[10] == Mykonos, city_end[10] == Mykonos))
    
    # Seville: must be occupied entirely from day 13 to 17 (index 12 to 16)
    for i in [12, 13, 14, 15, 16]:
        s.add(city_start[i] == Seville)
        s.add(city_end[i] == Seville)
    # And not in Seville on other days
    for i in range(num_days):
        if i not in [12, 13, 14, 15, 16]:
            s.add(city_start[i] != Seville)
            s.add(city_end[i] != Seville)
    
    # Frankfurt: must be in Frankfurt at least one day between day 1 and 5 (index 0 to 4)
    s.add(Or([Or(city_start[i] == Frankfurt, city_end[i] == Frankfurt) for i in range(0, 5)]))
    
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
            start_val = m.evaluate(city_start[i])
            end_val = m.evaluate(city_end[i])
            start_name = city_str(start_val)
            end_name = city_str(end_val)
            print(f"{i+1}\t{start_name}\t{end_name}")
    else:
        print("No valid plan found.")

if __name__ == '__main__':
    main()