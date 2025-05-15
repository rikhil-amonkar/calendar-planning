from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Venice': 0,
        'London': 1,
        'Lisbon': 2,
        'Brussels': 3,
        'Reykjavik': 4,
        'Santorini': 5,
        'Madrid': 6
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 3, 5, 6],  # Venice
        1: [0, 2, 4, 5, 6],  # London
        2: [0, 1, 3, 4, 6],  # Lisbon
        3: [0, 1, 2, 4, 6],  # Brussels
        4: [1, 2, 3, 6],  # Reykjavik
        5: [0, 1, 6],  # Santorini
        6: [0, 1, 2, 4, 5]  # Madrid
    }
    
    # Required days in each city
    required_days = {
        0: 3,  # Venice
        1: 3,  # London
        2: 4,  # Lisbon
        3: 2,  # Brussels
        4: 3,  # Reykjavik
        5: 3,  # Santorini
        6: 5   # Madrid
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(17)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Conference in Brussels (days 1-2)
    s.add(days[0] == 3)
    s.add(days[1] == 3)
    
    # Visit relatives in Venice (days 5-7)
    for i in range(4, 7):
        s.add(days[i] == 0)
    
    # Wedding in Madrid (days 7-11)
    for i in range(6, 11):
        s.add(days[i] == 6)
    
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