from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Prague': 0,
        'Warsaw': 1,
        'Dublin': 2,
        'Athens': 3,
        'Vilnius': 4,
        'Porto': 5,
        'London': 6,
        'Seville': 7,
        'Lisbon': 8,
        'Dubrovnik': 9
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [2, 3, 6, 8, 1],  # Prague
        1: [0, 3, 4, 5, 6, 8],  # Warsaw
        2: [3, 5, 6, 7, 8, 9],  # Dublin
        3: [0, 1, 2, 4, 6, 8, 9],  # Athens
        4: [1, 3],  # Vilnius
        5: [1, 2, 7, 8],  # Porto
        6: [0, 1, 2, 3, 8],  # London
        7: [2, 5, 8],  # Seville
        8: [0, 1, 2, 3, 5, 6, 7],  # Lisbon
        9: [2, 3]  # Dubrovnik
    }
    
    # Required days in each city
    required_days = {
        0: 3,  # Prague
        1: 4,  # Warsaw
        2: 3,  # Dublin
        3: 3,  # Athens
        4: 4,  # Vilnius
        5: 5,  # Porto
        6: 3,  # London
        7: 2,  # Seville
        8: 5,  # Lisbon
        9: 3   # Dubrovnik
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(26)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Workshop in Prague (days 1-3)
    for i in range(3):
        s.add(days[i] == 0)
    
    # Meet friends in Warsaw (days 20-23)
    for i in range(19, 23):
        s.add(days[i] == 1)
    
    # Conference in Porto (days 16 and 20)
    s.add(Or(days[15] == 5, days[19] == 5))
    
    # Wedding in London (days 3-5)
    for i in range(2, 5):
        s.add(days[i] == 6)
    
    # Visit relatives in Lisbon (days 5-9)
    for i in range(4, 9):
        s.add(days[i] == 8)
    
    # Flight constraints between consecutive days
    for i in range(25):
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
        for i in range(26):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()