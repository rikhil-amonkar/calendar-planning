from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Istanbul': 0,
        'Rome': 1,
        'Seville': 2,
        'Naples': 3,
        'Santorini': 4
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 3],  # Istanbul
        1: [0, 2, 3, 4],  # Rome
        2: [1],  # Seville
        3: [0, 1, 4],  # Naples
        4: [1, 3]  # Santorini
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Istanbul
        1: 3,  # Rome
        2: 4,  # Seville
        3: 7,  # Naples
        4: 4   # Santorini
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(16)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Visit relatives in Istanbul (days 6-7)
    s.add(days[5] == 0)
    s.add(days[6] == 0)
    
    # Wedding in Santorini (days 13-16)
    for i in range(12, 16):
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