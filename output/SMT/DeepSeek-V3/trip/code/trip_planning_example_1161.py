from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Mykonos': 0,
        'Krakow': 1,
        'Vilnius': 2,
        'Helsinki': 3,
        'Dubrovnik': 4,
        'Oslo': 5,
        'Madrid': 6,
        'Paris': 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [6],  # Mykonos
        1: [2, 5, 7],  # Krakow
        2: [1, 3, 5, 7],  # Vilnius
        3: [2, 4, 5, 6, 7],  # Helsinki
        4: [3, 5, 6],  # Dubrovnik
        5: [1, 2, 3, 4, 6, 7],  # Oslo
        6: [0, 1, 3, 4, 5, 7],  # Madrid
        7: [1, 2, 3, 5, 6]  # Paris
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Mykonos
        1: 5,  # Krakow
        2: 2,  # Vilnius
        3: 2,  # Helsinki
        4: 3,  # Dubrovnik
        5: 2,  # Oslo
        6: 5,  # Madrid
        7: 2   # Paris
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(18)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Visit relatives in Mykonos (days 15-18)
    for i in range(14, 18):
        s.add(days[i] == 0)
    
    # Annual show in Dubrovnik (days 2-4)
    for i in range(1, 4):
        s.add(days[i] == 4)
    
    # Meet friends in Oslo (days 1-2)
    s.add(days[0] == 5)
    s.add(days[1] == 5)
    
    # Flight constraints between consecutive days
    for i in range(17):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(next_day == current, 
               And(next_day != current, 
                   Or([next_day == dest for dest in direct_flights[current]]))))
    
    # Total days in each city must match requirements
    for city in cities.values():
        total = Sum([If(day == city, 1, 0) for day in days])
        s.add(total == required_days[city])
    
    # Solve and print schedule
    if s.check() == sat:
        m = s.model()
        schedule = [m[day].as_long() for day in days]
        print("Day\tCity")
        for i in range(18):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()