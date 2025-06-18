from z3 import *

def main():
    # Travel days: T1 to T6
    T1, T2, T3, T4, T5, T6 = Ints('T1 T2 T3 T4 T5 T6')
    T = [T1, T2, T3, T4, T5, T6]  # T[0]=T1, T[1]=T2, ..., T[5]=T6
    
    # Positions: 7 variables for the order of cities
    pos = [Int('pos_%d' % i) for i in range(7)]
    s = Solver()
    
    # Each position variable is between 0 and 6 (inclusive)
    for i in range(7):
        s.add(pos[i] >= 0)
        s.add(pos[i] <= 6)
    s.add(Distinct(pos))
    
    # City names and their required days
    city_names = ["Bucharest", "Venice", "Prague", "Frankfurt", "Zurich", "Florence", "Tallinn"]
    days_req = [3, 5, 4, 5, 5, 5, 5]  # Bucharest:3, Venice:5, Prague:4, Frankfurt:5, Zurich:5, Florence:5, Tallinn:5
    
    # Constraints for travel days: strictly increasing and within [2, 25]
    s.add(T1 >= 2, T1 <= 25)
    s.add(T2 > T1, T2 >= 3, T2 <= 25)
    s.add(T3 > T2, T3 >= 4, T3 <= 25)
    s.add(T4 > T3, T4 >= 5, T4 <= 25)
    s.add(T5 > T4, T5 >= 6, T5 <= 25)
    s.add(T6 > T5, T6 >= 7, T6 <= 25)
    
    # Constraints from the stay durations
    s.add(T1 == days_req[pos[0]])
    s.add(T2 == T1 + days_req[pos[1]] - 1)
    s.add(T3 == T2 + days_req[pos[2]] - 1)
    s.add(T4 == T3 + days_req[pos[3]] - 1)
    s.add(T5 == T4 + days_req[pos[4]] - 1)
    s.add(T6 == T5 + days_req[pos[5]] - 1)
    s.add(26 - T6 + 1 == days_req[pos[6]])  # Last city from T6 to day 26
    
    # Flight constraints: allowed direct flights
    # City indices: 0=Bucharest, 1=Venice, 2=Prague, 3=Frankfurt, 4=Zurich, 5=Florence, 6=Tallinn
    undirected_edges = [
        (2, 6), (6, 2),  # Prague and Tallinn
        (2, 4), (4, 2),  # Prague and Zurich
        (5, 2), (2, 5),  # Florence and Prague
        (3, 0), (0, 3),  # Frankfurt and Bucharest
        (3, 1), (1, 3),  # Frankfurt and Venice
        (2, 0), (0, 2),  # Prague and Bucharest
        (0, 4), (4, 0),  # Bucharest and Zurich
        (6, 3), (3, 6)   # Tallinn and Frankfurt
    ]
    directed_edges = [(4, 5)]  # Zurich to Florence
    allowed_flights = set(undirected_edges) | set(directed_edges)
    
    # For each consecutive city pair, ensure there is a direct flight
    for i in range(6):
        from_city = pos[i]
        to_city = pos[i+1]
        constraints = []
        for (x, y) in allowed_flights:
            constraints.append(And(from_city == x, to_city == y))
        s.add(Or(constraints))
    
    # Event constraints
    venice_index = 1
    frankfurt_index = 3
    tallinn_index = 6
    
    # Venice: must be in Venice on at least one day between 22 and 26
    venice_constraint = True
    for i in range(7):
        if i < 6:  # Cities in positions 0 to 5
            # Departure day T[i] must be >=22
            venice_constraint = And(venice_constraint, If(pos[i] == venice_index, T[i] >= 22, True))
    s.add(venice_constraint)
    
    # Frankfurt: must be in Frankfurt on at least one day between 12 and 16
    frankfurt_constraint = True
    for i in range(7):
        if i == 0:
            # First city: departure day T1 >=12
            clause = If(pos[0] == frankfurt_index, T[0] >= 12, True)
        elif i == 6:
            # Last city: arrival day T6 <=16
            clause = If(pos[6] == frankfurt_index, T[5] <= 16, True)
        else:
            # Middle cities: arrival day T[i-1] <=16 and departure day T[i] >=12
            clause = If(pos[i] == frankfurt_index, And(T[i-1] <= 16, T[i] >= 12), True)
        frankfurt_constraint = And(frankfurt_constraint, clause)
    s.add(frankfurt_constraint)
    
    # Tallinn: must be in Tallinn on at least one day between 8 and 12
    tallinn_constraint = True
    for i in range(7):
        if i == 0:
            clause = If(pos[0] == tallinn_index, T[0] >= 8, True)
        elif i == 6:
            clause = If(pos[6] == tallinn_index, T[5] <= 12, True)
        else:
            clause = If(pos[i] == tallinn_index, And(T[i-1] <= 12, T[i] >= 8), True)
        tallinn_constraint = And(tallinn_constraint, clause)
    s.add(tallinn_constraint)
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        # Extract the travel days and city order
        T_val = [m.evaluate(T[i]).as_long() for i in range(6)]
        pos_val = [m.evaluate(pos[i]).as_long() for i in range(7)]
        
        # Calculate start and end days for each city
        starts = [1]
        ends = [T_val[0]]
        for i in range(1, 6):
            starts.append(T_val[i-1])
            ends.append(T_val[i])
        starts.append(T_val[5])
        ends.append(26)
        
        # Print the itinerary
        for i in range(7):
            city_idx = pos_val[i]
            print(f"From day {starts[i]} to day {ends[i]}: {city_names[city_idx]}")
        
        # Print the flights
        for i in range(6):
            from_city = city_names[pos_val[i]]
            to_city = city_names[pos_val[i+1]]
            print(f"On day {T_val[i]}, fly from {from_city} to {to_city}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()