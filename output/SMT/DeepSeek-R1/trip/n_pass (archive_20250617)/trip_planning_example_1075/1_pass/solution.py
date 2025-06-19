from z3 import *

def main():
    s = Solver()
    
    # City mapping
    Reykjavik = 0
    Stuttgart = 1
    Vienna = 2
    Lyon = 3
    Edinburgh = 4
    Manchester = 5
    Split = 6
    Prague = 7
    
    city_names = {
        0: "Reykjavik",
        1: "Stuttgart",
        2: "Vienna",
        3: "Lyon",
        4: "Edinburgh",
        5: "Manchester",
        6: "Split",
        7: "Prague"
    }
    
    required_days = [5, 5, 4, 3, 4, 2, 5, 4]  # [0:Rey,1:Stutt,2:Vienna,3:Lyon,4:Edin,5:Manch,6:Split,7:Prague]
    
    edges_list = [
        (0,1), (0,2), (0,7),
        (1,2), (1,4), (1,5), (1,6),
        (2,3), (2,5), (2,6), (2,7),
        (3,6), (3,7),
        (4,7),
        (5,6), (5,7),
        (6,7)
    ]
    directed_edges = []
    for (a, b) in edges_list:
        directed_edges.append((a, b))
        directed_edges.append((b, a))
    
    num_days = 25
    num_flights = num_days - 1
    
    start_city = [Int('start_city_%d' % i) for i in range(num_days)]
    flight = [Bool('flight_%d' % i) for i in range(num_flights)]
    
    # Domain constraint for start_city
    for i in range(num_days):
        s.add(start_city[i] >= 0, start_city[i] <= 7)
    
    # Flight and next city constraints
    for i in range(num_flights):
        options = []
        for (x, y) in directed_edges:
            options.append(And(start_city[i] == x, start_city[i+1] == y))
        s.add(If(flight[i],
                 Or(options),
                 start_city[i] == start_city[i+1]))
    
    # Total flights must be 7
    s.add(Sum([If(flight[i], 1, 0) for i in range(num_flights)]) == 7)
    
    # Count for each city
    for c in range(8):
        base_count = Sum([If(start_city[i] == c, 1, 0) for i in range(num_days)])
        flight_count = Sum([If(And(flight[i], start_city[i+1] == c), 1, 0) for i in range(num_flights)])
        total_count = base_count + flight_count
        s.add(total_count == required_days[c])
    
    # Fixed Edinburgh from day5 to day8 (indices 4 to 7 for start_city, and no flights during days 5,6,7 (indices 4,5,6 in flight array)
    s.add(start_city[4] == Edinburgh)
    s.add(start_city[5] == Edinburgh)
    s.add(start_city[6] == Edinburgh)
    s.add(start_city[7] == Edinburgh)
    s.add(flight[4] == False)  # no flight at the end of day5
    s.add(flight[5] == False)  # no flight at the end of day6
    s.add(flight[6] == False)  # no flight at the end of day7
    
    # Split wedding: must be in Split on at least one day between 19 to 23 (start_city indices 18 to 22)
    conditions = []
    # For day19 (start_city index 18)
    conditions.append(Or(start_city[18] == Split, And(flight[18], start_city[19] == Split)))
    # For day20 (start_city index 19)
    conditions.append(Or(start_city[19] == Split, And(flight[19], start_city[20] == Split)))
    # For day21 (start_city index 20)
    conditions.append(Or(start_city[20] == Split, And(flight[20], start_city[21] == Split)))
    # For day22 (start_city index 21)
    conditions.append(Or(start_city[21] == Split, And(flight[21], start_city[22] == Split)))
    # For day23 (start_city index 22)
    conditions.append(Or(start_city[22] == Split, And(flight[22], start_city[23] == Split)))
    s.add(Or(conditions))
    
    if s.check() == sat:
        m = s.model()
        schedule_start = [m.evaluate(start_city[i]) for i in range(num_days)]
        schedule_flight = [m.evaluate(flight[i]) for i in range(num_flights)]
        
        for day in range(num_days):
            idx = day
            city_start = schedule_start[idx]
            city_start_val = city_start.as_long()
            if day < num_flights and is_true(schedule_flight[day]):
                city_next = schedule_start[day+1]
                city_next_val = city_next.as_long()
                print(f"Day {day+1}: Start in {city_names[city_start_val]}, then fly to {city_names[city_next_val]}")
            else:
                print(f"Day {day+1}: Stay in {city_names[city_start_val]}")
    else:
        print("No solution found")

if __name__ == '__main__':
    main()