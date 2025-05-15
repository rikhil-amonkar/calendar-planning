from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Zurich': 0,
        'Bucharest': 1,
        'Hamburg': 2,
        'Barcelona': 3,
        'Reykjavik': 4,
        'Stuttgart': 5,
        'Stockholm': 6,
        'Tallinn': 7,
        'Milan': 8,
        'London': 9
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 3, 4, 6, 7, 8, 9],  # Zurich
        1: [0, 2, 3, 9],  # Bucharest
        2: [0, 1, 3, 5, 6, 8, 9],  # Hamburg
        3: [0, 1, 2, 4, 5, 6, 7, 8, 9],  # Barcelona
        4: [0, 2, 3, 5, 6, 8, 9],  # Reykjavik
        5: [0, 2, 3, 4, 6, 7, 8, 9],  # Stuttgart
        6: [0, 2, 3, 4, 5, 7, 8, 9],  # Stockholm
        7: [0, 3, 5, 6],  # Tallinn
        8: [0, 2, 3, 4, 5, 6, 9],  # Milan
        9: [0, 1, 2, 3, 4, 5, 6, 8]  # London
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Zurich
        1: 2,  # Bucharest
        2: 5,  # Hamburg
        3: 4,  # Barcelona
        4: 5,  # Reykjavik
        5: 5,  # Stuttgart
        6: 2,  # Stockholm
        7: 4,  # Tallinn
        8: 5,  # Milan
        9: 3   # London
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(28)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Conference in Zurich (days 7-8)
    s.add(days[6] == 0)
    s.add(days[7] == 0)
    
    # Visit relatives in Reykjavik (days 9-13)
    for i in range(8, 13):
        s.add(days[i] == 4)
    
    # Meet friends in Milan (days 3-7)
    for i in range(2, 7):
        s.add(days[i] == 8)
    
    # Annual show in London (days 1-3)
    for i in range(3):
        s.add(days[i] == 9)
    
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