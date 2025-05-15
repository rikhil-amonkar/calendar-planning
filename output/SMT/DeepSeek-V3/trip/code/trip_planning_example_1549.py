from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Prague': 0,
        'Tallinn': 1,
        'Warsaw': 2,
        'Porto': 3,
        'Naples': 4,
        'Milan': 5,
        'Lisbon': 6,
        'Santorini': 7,
        'Riga': 8,
        'Stockholm': 9
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 5, 6, 8, 9],  # Prague
        1: [0, 2, 8, 9],  # Tallinn
        2: [0, 1, 3, 4, 5, 6, 8, 9],  # Warsaw
        3: [2, 5, 6],  # Porto
        4: [2, 5, 6, 7],  # Naples
        5: [0, 2, 3, 4, 6, 7, 8, 9],  # Milan
        6: [0, 2, 3, 4, 5, 7, 8, 9],  # Lisbon
        7: [4, 5, 6, 9],  # Santorini
        8: [0, 1, 2, 5, 6, 9],  # Riga
        9: [0, 1, 2, 5, 6, 7, 8]  # Stockholm
    }
    
    # Required days in each city
    required_days = {
        0: 5,  # Prague
        1: 3,  # Tallinn
        2: 2,  # Warsaw
        3: 3,  # Porto
        4: 5,  # Naples
        5: 3,  # Milan
        6: 5,  # Lisbon
        7: 5,  # Santorini
        8: 4,  # Riga
        9: 2   # Stockholm
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(28)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Visit relatives in Tallinn (days 18-20)
    for i in range(17, 20):
        s.add(days[i] == 1)
    
    # Meet friend in Milan (days 24-26)
    for i in range(23, 26):
        s.add(days[i] == 5)
    
    # Annual show in Riga (days 5-8)
    for i in range(4, 8):
        s.add(days[i] == 8)
    
    # Flight constraints between consecutive days
    for i in range(27):
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
        for i in range(28):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()