from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Seville': 0,
        'Vilnius': 1,
        'Santorini': 2,
        'London': 3,
        'Stuttgart': 4,
        'Dublin': 5,
        'Frankfurt': 6
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [5],  # Seville
        1: [6],  # Vilnius
        2: [3, 5],  # Santorini
        3: [2, 4, 5, 6],  # London
        4: [3, 6],  # Stuttgart
        5: [0, 2, 3, 6],  # Dublin
        6: [1, 3, 4, 5]  # Frankfurt
    }
    
    # Required days in each city
    required_days = {
        0: 5,  # Seville
        1: 3,  # Vilnius
        2: 2,  # Santorini
        3: 2,  # London
        4: 3,  # Stuttgart
        5: 3,  # Dublin
        6: 5   # Frankfurt
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(17)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Meet friends in London (days 9-10)
    s.add(days[8] == 3)
    s.add(days[9] == 3)
    
    # Visit relatives in Stuttgart (days 7-9)
    for i in range(6, 9):
        s.add(days[i] == 4)
    
    # Flight constraints between consecutive days
    for i in range(16):
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
        for i in range(17):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()