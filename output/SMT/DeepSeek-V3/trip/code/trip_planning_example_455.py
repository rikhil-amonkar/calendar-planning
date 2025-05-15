from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Reykjavik': 0,
        'Riga': 1,
        'Warsaw': 2,
        'Istanbul': 3,
        'Krakow': 4
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [2],  # Reykjavik
        1: [2, 3],  # Riga
        2: [0, 1, 3, 4],  # Warsaw
        3: [1, 2, 4],  # Istanbul
        4: [2, 3]  # Krakow
    }
    
    # Required days in each city
    required_days = {
        0: 7,  # Reykjavik
        1: 2,  # Riga
        2: 3,  # Warsaw
        3: 6,  # Istanbul
        4: 7   # Krakow
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(21)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Meet friend in Riga (days 1-2)
    s.add(days[0] == 1)
    s.add(days[1] == 1)
    
    # Wedding in Istanbul (days 2-7)
    for i in range(1, 7):
        s.add(days[i] == 3)
    
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