from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Istanbul': 0,
        'Vienna': 1,
        'Riga': 2,
        'Brussels': 3,
        'Madrid': 4,
        'Vilnius': 5,
        'Venice': 6,
        'Geneva': 7,
        'Munich': 8,
        'Reykjavik': 9
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 3, 4, 5, 6, 7, 8],  # Istanbul
        1: [0, 2, 3, 4, 5, 6, 7, 8, 9],  # Vienna
        2: [0, 3, 5, 8],  # Riga
        3: [0, 1, 2, 4, 5, 6, 7, 8, 9],  # Brussels
        4: [0, 1, 3, 6, 8, 9],  # Madrid
        5: [0, 1, 2, 3, 8],  # Vilnius
        6: [0, 1, 3, 4, 8],  # Venice
        7: [0, 1, 3, 4, 8],  # Geneva
        8: [0, 1, 2, 3, 4, 5, 6, 7, 9],  # Munich
        9: [1, 3, 4, 8]  # Reykjavik
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Istanbul
        1: 4,  # Vienna
        2: 2,  # Riga
        3: 2,  # Brussels
        4: 4,  # Madrid
        5: 4,  # Vilnius
        6: 5,  # Venice
        7: 4,  # Geneva
        8: 5,  # Munich
        9: 2   # Reykjavik
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(27)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Visit relatives in Geneva (days 1-4)
    for i in range(4):
        s.add(days[i] == 7)
    
    # Workshop in Venice (days 7-11)
    for i in range(6, 11):
        s.add(days[i] == 6)
    
    # Meet friends in Vilnius (days 20-23)
    for i in range(19, 23):
        s.add(days[i] == 5)
    
    # Wedding in Brussels (days 26-27)
    s.add(days[25] == 3)
    s.add(days[26] == 3)
    
    # Flight constraints between consecutive days
    for i in range(26):
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
        for i in range(27):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()