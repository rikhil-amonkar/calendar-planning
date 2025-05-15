from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Brussels': 0,
        'Rome': 1,
        'Dubrovnik': 2,
        'Geneva': 3,
        'Budapest': 4,
        'Riga': 5,
        'Valencia': 6
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 3, 4, 5, 6],  # Brussels
        1: [0, 2, 3, 4, 5, 6],  # Rome
        2: [1, 3],  # Dubrovnik
        3: [0, 1, 2, 4, 6],  # Geneva
        4: [0, 1, 3],  # Budapest
        5: [0, 1],  # Riga
        6: [0, 1, 3]  # Valencia
    }
    
    # Required days in each city
    required_days = {
        0: 5,  # Brussels
        1: 2,  # Rome
        2: 3,  # Dubrovnik
        3: 5,  # Geneva
        4: 2,  # Budapest
        5: 4,  # Riga
        6: 2   # Valencia
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(17)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Workshop in Brussels (days 7-11)
    for i in range(6, 11):
        s.add(days[i] == 0)
    
    # Meet friends in Riga (days 4-7)
    for i in range(3, 7):
        s.add(days[i] == 5)
    
    # Meet friend in Budapest (days 16-17)
    s.add(days[15] == 4)
    s.add(days[16] == 4)
    
    # Flight constraints between consecutive days
    for i in range(16):
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
        for i in range(17):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()