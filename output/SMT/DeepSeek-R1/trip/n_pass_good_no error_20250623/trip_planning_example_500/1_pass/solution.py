from z3 import *

def main():
    # City names and their required days
    cities = ["Hamburg", "Munich", "Manchester", "Lyon", "Split"]
    req_days = [7, 6, 2, 2, 7]
    c_map = {city: idx for idx, city in enumerate(cities)}
    
    # Define allowed flights (directed)
    flights = []
    # Bidirectional flights
    bidirectional = [
        ("Split", "Munich"),
        ("Munich", "Manchester"),
        ("Hamburg", "Manchester"),
        ("Hamburg", "Munich"),
        ("Split", "Lyon"),
        ("Lyon", "Munich"),
        ("Hamburg", "Split")
    ]
    for a, b in bidirectional:
        flights.append((c_map[a], c_map[b]))
        flights.append((c_map[b], c_map[a]))
    # Directed flight from Manchester to Split
    flights.append((c_map["Manchester"], c_map["Split"]))
    
    # Initialize Z3 solver
    s = Solver()
    
    # Block variables: which city in each of the 5 blocks
    block = [Int(f'block_{i}') for i in range(5)]
    for i in range(5):
        s.add(block[i] >= 0, block[i] < 5)
    s.add(Distinct(block))
    
    # Start and end days for each block
    start = [Int(f'start_{i}') for i in range(5)]
    end = [Int(f'end_{i}') for i in range(5)]
    length = [Int(f'length_{i}') for i in range(5)]
    
    # Fixed constraints
    s.add(start[0] == 1)  # Start on day 1
    s.add(end[4] == 20)   # End on day 20
    # Manchester must be in block 4 (last block) from day 19 to 20
    s.add(block[4] == c_map["Manchester"])
    s.add(start[4] == 19, end[4] == 20)
    
    # Block continuity: end[i] = start[i+1]
    for i in range(4):
        s.add(end[i] == start[i+1])
    
    # Length of each block
    for i in range(5):
        s.add(length[i] == end[i] - start[i] + 1)
        s.add(length[i] >= 1)
    
    # Lyon must be in one of the first four blocks and span days 13-14
    lyon_constraints = []
    for i in range(4):  # Blocks 0 to 3
        lyon_constraints.append(And(block[i] == c_map["Lyon"], start[i] == 13, end[i] == 14))
    s.add(Or(lyon_constraints))
    
    # Total days per city
    for c_idx in range(5):
        total_days = 0
        for b_idx in range(5):
            total_days += If(block[b_idx] == c_idx, length[b_idx], 0)
        s.add(total_days == req_days[c_idx])
    
    # Flight constraints between consecutive blocks
    for i in range(4):
        valid_flight = Or([And(block[i] == f[0], block[i+1] == f[1]) for f in flights])
        s.add(valid_flight)
    
    # Check for solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(5):
            s_val = model.eval(start[i]).as_long()
            e_val = model.eval(end[i]).as_long()
            city_idx = model.eval(block[i]).as_long()
            city_name = cities[city_idx]
            itinerary.append({
                "day_range": f"Day {s_val}-{e_val}",
                "place": city_name
            })
            if i < 4:
                flight_day = e_val
                dep_city = city_name
                arr_city = cities[model.eval(block[i+1]).as_long()]
                itinerary.append({
                    "day_range": f"Day {flight_day}",
                    "place": dep_city
                })
                itinerary.append({
                    "day_range": f"Day {flight_day}",
                    "place": arr_city
                })
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()