from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Tallinn': 0,
        'Bucharest': 1,
        'Seville': 2,
        'Stockholm': 3,
        'Munich': 4,
        'Milan': 5
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [3, 4],  # Tallinn
        1: [4],  # Bucharest
        2: [4, 5],  # Seville
        3: [0, 4, 5],  # Stockholm
        4: [0, 1, 2, 3, 5],  # Munich
        5: [2, 3, 4]  # Milan
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Tallinn
        1: 4,  # Bucharest
        2: 5,  # Seville
        3: 5,  # Stockholm
        4: 5,  # Munich
        5: 2   # Milan
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..18)
    days = [Int(f'day_{i}') for i in range(18)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 6 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: visit relatives in Bucharest between days 1-4 (days 0-3 in 0-based)
    for i in range(4):
        s.add(days[i] == 1)
    
    # Constraint: wedding in Munich between days 4-8 (days 3-7 in 0-based)
    for i in range(3, 8):
        s.add(days[i] == 4)
    
    # Constraint: meet friends in Seville between days 8-12 (days 7-11 in 0-based)
    for i in range(7, 12):
        s.add(days[i] == 2)
    
    # Constraint: flights between consecutive days must be direct or same city
    for i in range(17):
        current_city = days[i]
        next_city = days[i+1]
        s.add(Or(next_city == current_city, 
                 And(next_city != current_city, 
                     Or([next_city == dest for dest in direct_flights[current_city]]))))
    
    # Constraint: total days in each city must match required_days
    for city in cities.values():
        total_days = Sum([If(day == city, 1, 0) for day in days])
        s.add(total_days == required_days[city])
    
    # Check if the problem is satisfiable
    if s.check() == sat:
        m = s.model()
        schedule = [m[day].as_long() for day in days]
        # Print the schedule
        print("Day\tCity")
        for i in range(18):
            print(f"{i+1}\t{city_names[schedule[i]]}")
    else:
        print("No valid trip plan found.")

solve_trip_planning()