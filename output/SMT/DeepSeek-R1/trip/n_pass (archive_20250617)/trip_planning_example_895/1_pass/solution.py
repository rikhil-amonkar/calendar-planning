from z3 import *

def main():
    # City indices
    # 0: Brussels, 1: Venice, 2: London, 3: Lisbon, 4: Reykjavik, 5: Santorini, 6: Madrid
    cities = {
        0: 'Brussels',
        1: 'Venice',
        2: 'London',
        3: 'Lisbon',
        4: 'Reykjavik',
        5: 'Santorini',
        6: 'Madrid'
    }
    
    # Required days per city index
    days_arr = [2, 3, 3, 4, 3, 3, 5]
    
    # Allowed directed flights (including bidirectional and directed flights)
    allowed_flights = [
        (0,1), (1,0),  # Brussels <-> Venice
        (0,2), (2,0),  # Brussels <-> London
        (0,3), (3,0),  # Brussels <-> Lisbon
        (0,4), (4,0),  # Brussels <-> Reykjavik
        (0,6), (6,0),  # Brussels <-> Madrid
        (1,2), (2,1),  # Venice <-> London
        (1,3), (3,1),  # Venice <-> Lisbon
        (1,5), (5,1),  # Venice <-> Santorini
        (1,6), (6,1),  # Venice <-> Madrid
        (2,3), (3,2),  # London <-> Lisbon
        (2,4), (4,2),  # London <-> Reykjavik
        (2,5), (5,2),  # London <-> Santorini
        (2,6), (6,2),  # London <-> Madrid
        (3,4), (4,3),  # Lisbon <-> Reykjavik
        (3,6), (6,3),  # Lisbon <-> Madrid
        (5,6), (6,5),  # Santorini <-> Madrid
        (4,6)           # Reykjavik -> Madrid (directed)
    ]
    
    # Initialize Z3 solver
    s = Solver()
    
    # Position variables: sequence of cities
    pos = [Int('pos_%d' % i) for i in range(7)]
    # Duration for each position
    d_arr = [Int('d_arr_%d' % i) for i in range(7)]
    # Start and end days for each city in the sequence
    start_days = [Int('start_%d' % i) for i in range(7)]
    end_days = [Int('end_%d' % i) for i in range(7)]
    
    # Fix first city to Brussels (index 0)
    s.add(pos[0] == 0)
    
    # All cities are distinct and in range 0-6
    s.add(Distinct(pos))
    for i in range(7):
        s.add(pos[i] >= 0, pos[i] <= 6)
    
    # Define d_arr: the duration for the city at each position
    for i in range(7):
        s.add(d_arr[i] == If(
            pos[i] == 0, days_arr[0],
            If(pos[i] == 1, days_arr[1],
            If(pos[i] == 2, days_arr[2],
            If(pos[i] == 3, days_arr[3],
            If(pos[i] == 4, days_arr[4],
            If(pos[i] == 5, days_arr[5], days_arr[6])))))
    
    # Define start and end days
    s.add(start_days[0] == 1)
    s.add(end_days[0] == start_days[0] + d_arr[0] - 1)
    
    for i in range(1, 7):
        s.add(start_days[i] == end_days[i-1])
        s.add(end_days[i] == start_days[i] + d_arr[i] - 1)
    
    # Flight constraints between consecutive cities
    for i in range(6):
        constraints = []
        for flight in allowed_flights:
            a, b = flight
            constraints.append(And(pos[i] == a, pos[i+1] == b))
        s.add(Or(constraints))
    
    # Event constraints
    # Venice (index 1) must have at least one day between day 5 and 7
    for i in range(7):
        s.add(Implies(pos[i] == 1, And(start_days[i] <= 7, end_days[i] >= 5)))
    
    # Madrid (index 6) must have at least one day between day 7 and 11
    for i in range(7):
        s.add(Implies(pos[i] == 6, And(start_days[i] <= 11, end_days[i] >= 7)))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        # Print the trip plan
        print("Trip Plan:")
        for i in range(7):
            city_index = model.evaluate(pos[i]).as_long()
            start = model.evaluate(start_days[i]).as_long()
            end = model.evaluate(end_days[i]).as_long()
            print(f"From day {start} to day {end}: {cities[city_index]}")
    else:
        print("No valid trip plan found.")

if __name__ == '__main__':
    main()