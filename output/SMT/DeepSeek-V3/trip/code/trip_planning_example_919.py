from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Vienna': 0,
        'Milan': 1,
        'Rome': 2,
        'Riga': 3,
        'Lisbon': 4,
        'Vilnius': 5,
        'Oslo': 6
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 3, 4, 5, 6],  # Vienna
        1: [0, 3, 4, 5, 6],  # Milan
        2: [0, 3, 4, 6],  # Rome
        3: [0, 1, 2, 4, 5, 6],  # Riga
        4: [0, 1, 2, 3, 6],  # Lisbon
        5: [0, 1, 3, 6],  # Vilnius
        6: [0, 1, 2, 3, 4, 5]  # Oslo
    }
    
    # Required days in each city
    required_days = {
        0: 4,  # Vienna
        1: 2,  # Milan
        2: 3,  # Rome
        3: 2,  # Riga
        4: 3,  # Lisbon
        5: 4,  # Vilnius
        6: 3   # Oslo
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(15)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Conference in Vienna (days 1-4)
    for i in range(4):
        s.add(days[i] == 0)
    
    # Visit relatives in Lisbon (days 11-13)
    for i in range(10, 13):
        s.add(days[i] == 4)
    
    # Meet friend in Oslo (days 13-15)
    for i in range(12, 15):
        s.add(days[i] == 6)
    
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