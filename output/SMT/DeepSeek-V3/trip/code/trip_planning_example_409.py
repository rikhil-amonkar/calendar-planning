from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Hamburg': 0,
        'Zurich': 1,
        'Helsinki': 2,
        'Bucharest': 3,
        'Split': 4
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 3, 4],  # Hamburg
        1: [0, 2, 3, 4],  # Zurich
        2: [0, 1, 4],  # Helsinki
        3: [0, 1],  # Bucharest
        4: [0, 1, 2]  # Split
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Hamburg
        1: 3,  # Zurich
        2: 2,  # Helsinki
        3: 2,  # Bucharest
        4: 7   # Split
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(12)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Wedding in Zurich (days 1-3)
    for i in range(3):
        s.add(days[i] == 1)
    
    # Conference in Split (days 4 and 10)
    s.add(Or(days[3] == 4, days[9] == 4))
    
    # Flight constraints between consecutive days
    for i in range(11):
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
        for i in range(12):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()