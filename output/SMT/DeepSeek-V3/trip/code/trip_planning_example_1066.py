from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Brussels': 0,
        'Bucharest': 1,
        'Stuttgart': 2,
        'Mykonos': 3,
        'Madrid': 4,
        'Helsinki': 5,
        'Split': 6,
        'London': 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 5, 7, 4],  # Brussels
        1: [0, 4, 7],  # Bucharest
        2: [6, 7],  # Stuttgart
        3: [4, 7],  # Mykonos
        4: [0, 1, 3, 5, 6, 7],  # Madrid
        5: [0, 4, 6, 7],  # Helsinki
        6: [4, 5, 7, 2],  # Split
        7: [0, 1, 2, 3, 4, 5, 6]  # London
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Brussels
        1: 3,  # Bucharest
        2: 4,  # Stuttgart
        3: 2,  # Mykonos
        4: 2,  # Madrid
        5: 5,  # Helsinki
        6: 3,  # Split
        7: 5   # London
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(21)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Meet friend in Stuttgart (days 1-4)
    for i in range(4):
        s.add(days[i] == 2)
    
    # Conference in Madrid (days 20-21)
    s.add(days[19] == 4)
    s.add(days[20] == 4)
    
    # Flight constraints between consecutive days
    for i in range(20):
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
        for i in range(21):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()