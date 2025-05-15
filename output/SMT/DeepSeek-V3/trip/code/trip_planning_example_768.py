from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Mykonos': 0,
        'Nice': 1,
        'London': 2,
        'Copenhagen': 3,
        'Oslo': 4,
        'Tallinn': 5
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2],  # Mykonos
        1: [0, 2, 3, 4],  # Nice
        2: [0, 1, 3, 4],  # London
        3: [1, 2, 4, 5],  # Copenhagen
        4: [1, 2, 3, 5],  # Oslo
        5: [3, 4]  # Tallinn
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Mykonos
        1: 3,  # Nice
        2: 2,  # London
        3: 3,  # Copenhagen
        4: 5,  # Oslo
        5: 4   # Tallinn
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(16)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Conference in Nice (days 14 and 16)
    s.add(days[13] == 1)
    s.add(days[15] == 1)
    
    # Meet friend in Oslo (days 10-14)
    for i in range(9, 14):
        s.add(days[i] == 4)
    
    # Flight constraints between consecutive days
    for i in range(15):
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
        for i in range(16):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()