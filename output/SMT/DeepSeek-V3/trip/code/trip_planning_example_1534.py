from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Warsaw': 0,
        'Venice': 1,
        'Vilnius': 2,
        'Salzburg': 3,
        'Amsterdam': 4,
        'Barcelona': 5,
        'Paris': 6,
        'Hamburg': 7,
        'Florence': 8,
        'Tallinn': 9
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 4, 5, 6, 7, 9],  # Warsaw
        1: [0, 4, 5, 6, 7],  # Venice
        2: [0, 4, 6, 9],  # Vilnius
        3: [7],  # Salzburg
        4: [0, 2, 5, 6, 7, 8, 9],  # Amsterdam
        5: [0, 4, 7, 8, 1, 9, 6],  # Barcelona
        6: [0, 1, 2, 4, 5, 7, 8, 9],  # Paris
        7: [0, 1, 4, 5, 6, 3],  # Hamburg
        8: [4, 5, 6],  # Florence
        9: [0, 2, 4, 5, 6]  # Tallinn
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Warsaw
        1: 3,  # Venice
        2: 3,  # Vilnius
        3: 4,  # Salzburg
        4: 2,  # Amsterdam
        5: 5,  # Barcelona
        6: 2,  # Paris
        7: 4,  # Hamburg
        8: 5,  # Florence
        9: 2   # Tallinn
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(25)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Workshop in Paris (days 1-2)
    s.add(days[0] == 6)
    s.add(days[1] == 6)
    
    # Meet friends in Barcelona (days 2-6)
    for i in range(1, 6):
        s.add(days[i] == 5)
    
    # Meet friend in Tallinn (days 11-12)
    s.add(days[10] == 9)
    s.add(days[11] == 9)
    
    # Conference in Hamburg (days 19-22)
    for i in range(18, 22):
        s.add(days[i] == 7)
    
    # Wedding in Salzburg (days 22-25)
    for i in range(21, 25):
        s.add(days[i] == 3)
    
    # Flight constraints between consecutive days
    for i in range(24):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(next_day == current, 
               And(next_day != current, 
                   Or([next_day == dest for dest in direct_flights[current]])))
    
    # Total days in each city must match requirements
    for city in cities.values():
        total = Sum([If(day == city, 1, 0) for day in days])
        s.add(total == required_days[city])
    
    # Solve and print schedule
    if s.check() == sat:
        m = s.model()
        schedule = [m[day].as_long() for day in days]
        print("Day\tCity")
        for i in range(25):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()