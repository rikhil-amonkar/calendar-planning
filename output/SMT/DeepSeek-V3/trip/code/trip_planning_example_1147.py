from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Brussels': 0,
        'Helsinki': 1,
        'Split': 2,
        'Dubrovnik': 3,
        'Istanbul': 4,
        'Milan': 5,
        'Vilnius': 6,
        'Frankfurt': 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 5, 6, 7],  # Brussels
        1: [0, 3, 5, 6, 7],  # Helsinki
        2: [1, 5, 6, 7],  # Split
        3: [1, 4, 7],  # Dubrovnik
        4: [0, 1, 5, 6, 7],  # Istanbul
        5: [0, 1, 2, 4, 6, 7],  # Milan
        6: [0, 1, 2, 4, 5, 7],  # Vilnius
        7: [0, 1, 2, 3, 4, 5, 6]  # Frankfurt
    }
    
    # Required days in each city
    required_days = {
        0: 3,  # Brussels
        1: 3,  # Helsinki
        2: 4,  # Split
        3: 2,  # Dubrovnik
        4: 5,  # Istanbul
        5: 4,  # Milan
        6: 5,  # Vilnius
        7: 3   # Frankfurt
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(22)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Annual show in Istanbul (days 1-5)
    for i in range(5):
        s.add(days[i] == 4)
    
    # Workshop in Vilnius (days 18-22)
    for i in range(17, 22):
        s.add(days[i] == 6)
    
    # Wedding in Frankfurt (days 16-18)
    for i in range(15, 18):
        s.add(days[i] == 7)
    
    # Flight constraints between consecutive days
    for i in range(21):
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
        for i in range(22):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()