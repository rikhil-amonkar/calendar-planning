from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Lisbon': 0,
        'Dubrovnik': 1,
        'Copenhagen': 2,
        'Prague': 3,
        'Tallinn': 4,
        'Stockholm': 5,
        'Split': 6,
        'Lyon': 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [2, 3, 5, 7],  # Lisbon
        1: [2, 5],  # Dubrovnik
        2: [0, 1, 3, 4, 5, 6],  # Copenhagen
        3: [0, 2, 4, 5, 6, 7],  # Prague
        4: [2, 3, 5],  # Tallinn
        5: [0, 1, 2, 3, 4, 6],  # Stockholm
        6: [2, 3, 5, 7],  # Split
        7: [0, 3, 6]  # Lyon
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Lisbon
        1: 5,  # Dubrovnik
        2: 5,  # Copenhagen
        3: 3,  # Prague
        4: 2,  # Tallinn
        5: 4,  # Stockholm
        6: 3,  # Split
        7: 2   # Lyon
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(19)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Workshop in Lisbon (days 4-5)
    s.add(days[3] == 0)
    s.add(days[4] == 0)
    
    # Meet friend in Tallinn (days 1-2)
    s.add(days[0] == 4)
    s.add(days[1] == 4)
    
    # Wedding in Stockholm (days 13-16)
    for i in range(12, 16):
        s.add(days[i] == 5)
    
    # Annual show in Lyon (days 18-19)
    s.add(days[17] == 7)
    s.add(days[18] == 7)
    
    # Flight constraints between consecutive days
    for i in range(18):
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
        for i in range(19):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()