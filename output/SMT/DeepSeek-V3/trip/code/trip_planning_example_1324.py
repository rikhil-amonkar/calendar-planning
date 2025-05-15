from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Venice': 0,
        'Barcelona': 1,
        'Copenhagen': 2,
        'Lyon': 3,
        'Reykjavik': 4,
        'Dubrovnik': 5,
        'Athens': 6,
        'Tallinn': 7,
        'Munich': 8
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 6, 8],  # Venice
        1: [0, 2, 3, 4, 5, 6, 7, 8],  # Barcelona
        2: [0, 1, 4, 5, 6, 7, 8],  # Copenhagen
        3: [1, 0, 8],  # Lyon
        4: [1, 2, 6, 8],  # Reykjavik
        5: [1, 2, 6, 8],  # Dubrovnik
        6: [0, 1, 2, 4, 5, 8],  # Athens
        7: [1, 2, 8],  # Tallinn
        8: [0, 1, 2, 3, 4, 5, 6, 7]  # Munich
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Venice
        1: 3,  # Barcelona
        2: 4,  # Copenhagen
        3: 4,  # Lyon
        4: 4,  # Reykjavik
        5: 5,  # Dubrovnik
        6: 2,  # Athens
        7: 5,  # Tallinn
        8: 3   # Munich
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(26)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Meet friend in Barcelona (days 10-12)
    for i in range(9, 12):
        s.add(days[i] == 1)
    
    # Visit relatives in Copenhagen (days 7-10)
    for i in range(6, 10):
        s.add(days[i] == 2)
    
    # Wedding in Dubrovnik (days 16-20)
    for i in range(15, 20):
        s.add(days[i] == 5)
    
    # Flight constraints between consecutive days
    for i in range(25):
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
        for i in range(26):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()