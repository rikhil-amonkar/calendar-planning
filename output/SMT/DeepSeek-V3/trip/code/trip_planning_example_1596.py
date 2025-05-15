from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Bucharest': 0,
        'Krakow': 1,
        'Munich': 2,
        'Barcelona': 3,
        'Warsaw': 4,
        'Budapest': 5,
        'Stockholm': 6,
        'Riga': 7,
        'Edinburgh': 8,
        'Vienna': 9
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 4, 5, 7, 9],  # Bucharest
        1: [0, 2, 4, 6, 8, 9],  # Krakow
        2: [0, 1, 3, 4, 5, 6, 7, 8, 9],  # Munich
        3: [1, 2, 4, 5, 6, 7, 8, 9],  # Barcelona
        4: [0, 1, 2, 3, 5, 6, 7, 9],  # Warsaw
        5: [0, 2, 3, 4, 6, 7, 8, 9],  # Budapest
        6: [1, 2, 3, 4, 5, 7, 8, 9],  # Stockholm
        7: [0, 2, 3, 4, 5, 6, 8, 9],  # Riga
        8: [1, 2, 3, 5, 6, 7],  # Edinburgh
        9: [0, 1, 2, 3, 4, 5, 6, 7]  # Vienna
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Bucharest
        1: 4,  # Krakow
        2: 3,  # Munich
        3: 5,  # Barcelona
        4: 5,  # Warsaw
        5: 5,  # Budapest
        6: 2,  # Stockholm
        7: 5,  # Riga
        8: 5,  # Edinburgh
        9: 5   # Vienna
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(32)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Workshop in Munich (days 18-20)
    for i in range(17, 20):
        s.add(days[i] == 2)
    
    # Conference in Warsaw (days 25-29)
    for i in range(24, 29):
        s.add(days[i] == 4)
    
    # Annual show in Budapest (days 9-13)
    for i in range(8, 13):
        s.add(days[i] == 5)
    
    # Meet friends in Stockholm (days 17-18)
    s.add(days[16] == 6)
    s.add(days[17] == 6)
    
    # Meet friend in Edinburgh (days 1-5)
    for i in range(5):
        s.add(days[i] == 8)
    
    # Flight constraints between consecutive days
    for i in range(31):
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
        for i in range(32):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()