from z3 import *

def solve_trip_planning():
    # Cities and their codes for easier reference
    cities = {
        'Porto': 0,
        'Geneva': 1,
        'Mykonos': 2,
        'Manchester': 3,
        'Hamburg': 4,
        'Naples': 5,
        'Frankfurt': 6
    }
    city_names = {v: k for k, v in cities.items()}
    
    # Direct flights: adjacency list
    direct_flights = {
        0: [1, 3, 4, 6],  # Porto
        1: [0, 2, 3, 4, 5, 6],  # Geneva
        2: [1, 3, 5],  # Mykonos
        3: [0, 1, 2, 4, 5, 6],  # Manchester
        4: [0, 1, 3, 5, 6],  # Hamburg
        5: [1, 2, 3, 4, 6],  # Naples
        6: [0, 1, 3, 4, 5]  # Frankfurt
    }
    
    # Required days in each city
    required_days = {
        0: 2,  # Porto
        1: 3,  # Geneva
        2: 3,  # Mykonos
        3: 4,  # Manchester
        4: 5,  # Hamburg
        5: 5,  # Naples
        6: 2   # Frankfurt
    }
    
    # Create Z3 variables: day[i] is the city on day i+1 (days 1..18)
    days = [Int(f'day_{i}') for i in range(18)]
    
    s = Solver()
    
    # Constraint: each day's city must be one of the 7 cities
    for day in days:
        s.add(Or([day == c for c in cities.values()]))
    
    # Constraint: annual show in Frankfurt between days 5-6 (days 4-5 in 0-based)
    s.add(days[4] == 6)
    s.add(days[5] == 6)
    
    # Constraint: meet friend in Mykonos between days 10-12 (days 9-11 in 0-based)
    for i in range(9, 12):
        s.add(days[i] == 2)
    
    # Constraint: wedding in Manchester between days 15-18 (days 14-17 in 0-based)
    for i in range(14, 18):
        s.add(days[i] == 3)
    
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