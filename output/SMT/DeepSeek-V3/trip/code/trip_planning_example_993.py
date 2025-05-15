from z3 import *

def solve_trip_planning():
    # Cities and their codes
    cities = {
        'Riga': 0,
        'Frankfurt': 1,
        'Amsterdam': 2,
        'Vilnius': 3,
        'London': 4,
        'Stockholm': 5,
        'Bucharest': 6
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flight connections
    direct_flights = {
        0: [1, 2, 3, 5, 6],  # Riga
        1: [0, 2, 3, 4, 5, 6],  # Frankfurt
        2: [0, 1, 3, 4, 5, 6],  # Amsterdam
        3: [0, 1, 2],  # Vilnius
        4: [1, 2, 5, 6],  # London
        5: [0, 1, 2, 4],  # Stockholm
        6: [0, 1, 2, 4]  # Bucharest
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Riga
        1: 3,  # Frankfurt
        2: 2,  # Amsterdam
        3: 5,  # Vilnius
        4: 2,  # London
        5: 3,  # Stockholm
        6: 4   # Bucharest
    }
    
    # Create Z3 variables for each day
    days = [Int(f'day_{i}') for i in range(15)]
    s = Solver()
    
    # Each day must be one of the cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Event constraints
    # Meet friend in Amsterdam (days 2-3)
    s.add(days[1] == 2)
    s.add(days[2] == 2)
    
    # Workshop in Vilnius (days 7-11)
    for i in range(6, 11):
        s.add(days[i] == 3)
    
    # Wedding in Stockholm (days 13-15)
    for i in range(12, 15):
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