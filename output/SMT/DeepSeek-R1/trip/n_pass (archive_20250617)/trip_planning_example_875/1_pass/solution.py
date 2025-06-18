from z3 import *

def main():
    # Define city mapping to integers
    cities = {
        'Stuttgart': 0,
        'Edinburgh': 1,
        'Athens': 2,
        'Split': 3,
        'Krakow': 4,
        'Venice': 5,
        'Mykonos': 6
    }
    
    # Define allowed direct flight pairs (both directions)
    allowed_pairs = set()
    pairs = [(0,1), (0,2), (0,3), (0,4), (0,5), (1,2), (1,4), (1,5), (2,3), (2,5), (2,6), (3,4)]
    for a, b in pairs:
        allowed_pairs.add((a, b))
        allowed_pairs.add((b, a))
    
    # Initialize Z3 solver
    s = Solver()
    
    # Create variables for each day (0 to 19 representing days 1 to 20)
    city_start = [Int(f'city_start_{i}') for i in range(20)]
    flight_taken = [Bool(f'flight_taken_{i}') for i in range(20)]
    flight_dest = [Int(f'flight_dest_{i}') for i in range(20)]
    
    # Add constraints for city and flight destination values (0 to 6)
    for i in range(20):
        s.add(city_start[i] >= 0, city_start[i] <= 6)
        s.add(flight_dest[i] >= 0, flight_dest[i] <= 6)
    
    # Next day start city constraints
    for i in range(19):
        s.add(If(flight_taken[i], city_start[i+1] == flight_dest[i], city_start[i+1] == city_start[i]))
    
    # Flight constraints: only allowed direct flights
    for i in range(20):
        s.add(Implies(flight_taken[i], Or([And(city_start[i] == a, flight_dest[i] == b) for (a, b) in allowed_pairs])))
    
    # Total days per city calculation
    total_days = [0] * 7
    for c in range(7):
        count_start = Sum([If(city_start[i] == c, 1, 0) for i in range(20)])
        count_flight_dest = Sum([If(And(flight_taken[i], flight_dest[i] == c), 1, 0) for i in range(20)])
        total_days[c] = count_start + count_flight_dest
    
    # Total days constraints
    s.add(total_days[0] == 3)  # Stuttgart
    s.add(total_days[1] == 4)  # Edinburgh
    s.add(total_days[2] == 4)  # Athens
    s.add(total_days[3] == 2)  # Split
    s.add(total_days[4] == 4)  # Krakow
    s.add(total_days[5] == 5)  # Venice
    s.add(total_days[6] == 4)  # Mykonos
    
    # Helper function to check city presence on a day
    def in_city(day_index, city_index):
        return Or(
            city_start[day_index] == city_index,
            And(flight_taken[day_index], flight_dest[day_index] == city_index)
        )
    
    # Event constraints
    s.add(Or(in_city(10, 0), in_city(11, 0), in_city(12, 0))  # Stuttgart workshop (days 11-13)
    s.add(Or(in_city(12, 3), in_city(13, 3))  # Split meeting (days 13-14)
    s.add(Or([in_city(i, 4) for i in [7, 8, 9, 10]]))  # Krakow meeting (days 8-11)
    
    # Solve and output the plan
    if s.check() == sat:
        m = s.model()
        idx_to_city = {v: k for k, v in cities.items()}
        plan = []
        for i in range(20):
            start_city_val = m.evaluate(city_start[i]).as_long()
            flight_taken_val = m.evaluate(flight_taken[i])
            if is_true(flight_taken_val):
                flight_dest_val = m.evaluate(flight_dest[i]).as_long()
                cities_today = [start_city_val, flight_dest_val]
                cities_today_names = [idx_to_city[c] for c in cities_today]
                plan.append(f"Day {i+1}: {', '.join(cities_today_names)}")
            else:
                plan.append(f"Day {i+1}: {idx_to_city[start_city_val]}")
        print("\n".join(plan))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()