from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Helsinki': 0,
        'Warsaw': 1,
        'Madrid': 2,
        'Split': 3,
        'Reykjavik': 4,
        'Budapest': 5
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 3, 4, 5],  # Helsinki
        1: [0, 2, 3, 4, 5],  # Warsaw
        2: [0, 1, 3, 4, 5],  # Madrid
        3: [0, 1, 2],  # Split
        4: [0, 1, 2, 5],  # Reykjavik
        5: [0, 1, 2, 4]  # Budapest
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Helsinki
        1: 3,  # Warsaw
        2: 4,  # Madrid
        3: 4,  # Split
        4: 2,  # Reykjavik
        5: 4   # Budapest
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(14)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Workshop in Helsinki (days 1-2)
    s.add(days[0] == 0)
    s.add(days[1] == 0)
    
    # Visit relatives in Warsaw (days 9-11)
    for i in range(8, 11):
        s.add(days[i] == 1)
    
    # Meet friend in Reykjavik (days 8-9)
    s.add(days[7] == 4)
    s.add(days[8] == 4)
    
    # Flight constraints between consecutive days
    for i in range(13):
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
        for i in range(14):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()