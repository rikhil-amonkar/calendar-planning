from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Dublin': 0,
        'Helsinki': 1,
        'Riga': 2,
        'Reykjavik': 3,
        'Vienna': 4,
        'Tallinn': 5
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 3, 4, 5],  # Dublin
        1: [0, 2, 3, 4, 5],  # Helsinki
        2: [0, 1, 4, 5],  # Riga
        3: [0, 1, 4],  # Reykjavik
        4: [0, 1, 2, 3],  # Vienna
        5: [0, 1, 2]  # Tallinn
    }
    
    # Required days in each city
    required_days = {
        0: 5,  # Dublin
        1: 3,  # Helsinki
        2: 3,  # Riga
        3: 2,  # Reykjavik
        4: 2,  # Vienna
        5: 5   # Tallinn
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(15)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Meet friends in Helsinki (days 3-5)
    for i in range(2, 5):
        s.add(days[i] == 1)
    
    # Annual show in Vienna (days 2-3)
    s.add(days[1] == 4)
    s.add(days[2] == 4)
    
    # Wedding in Tallinn (days 7-11)
    for i in range(6, 11):
        s.add(days[i] == 5)
    
    # Flight constraints between consecutive days
    for i in range(14):
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
        for i in range(15):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()