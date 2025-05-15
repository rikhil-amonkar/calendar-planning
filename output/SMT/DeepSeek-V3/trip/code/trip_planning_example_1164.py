from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Reykjavik': 0,
        'Stockholm': 1,
        'Porto': 2,
        'Nice': 3,
        'Venice': 4,
        'Vienna': 5,
        'Split': 6,
        'Copenhagen': 7
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 3, 5, 7],  # Reykjavik
        1: [0, 3, 5, 6, 7],  # Stockholm
        2: [3, 5, 7],  # Porto
        3: [0, 1, 2, 4, 5, 7],  # Nice
        4: [3, 5, 7],  # Venice
        5: [0, 1, 2, 3, 4, 6, 7],  # Vienna
        6: [1, 5, 7],  # Split
        7: [0, 1, 2, 3, 4, 5, 6]  # Copenhagen
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Reykjavik
        1: 2,  # Stockholm
        2: 5,  # Porto
        3: 3,  # Nice
        4: 4,  # Venice
        5: 3,  # Vienna
        6: 3,  # Split
        7: 2   # Copenhagen
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(17)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Meet friend in Reykjavik (days 3-4)
    s.add(days[2] == 0)
    s.add(days[3] == 0)
    
    # Meet friends in Stockholm (days 4-5)
    s.add(days[3] == 1)
    s.add(days[4] == 1)
    
    # Wedding in Porto (days 13-17)
    for i in range(12, 17):
        s.add(days[i] == 2)
    
    # Workshop in Vienna (days 11-13)
    for i in range(10, 13):
        s.add(days[i] == 5)
    
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