import json
from z3 import *

def main():
    # Define city data
    city_ids = {
        "Barcelona": 0,
        "Venice": 1,
        "Nice": 2,
        "Naples": 3,
        "Valencia": 4,
        "Stuttgart": 5,
        "Split": 6,
        "Amsterdam": 7,
        "Porto": 8
    }
    id_to_name = {v: k for k, v in city_ids.items()}
    
    required_days_list = [2, 5, 2, 3, 5, 2, 5, 4, 4]  # for ids 0 to 8
    
    # Allowed direct flight pairs (bidirectional)
    allowed_pairs = [
        (1, 2), (2, 1), (3, 7), (7, 3), (0, 2), (2, 0), (7, 2), (2, 7),
        (5, 4), (4, 5), (5, 8), (8, 5), (6, 5), (5, 6), (6, 3), (3, 6),
        (4, 7), (7, 4), (0, 8), (8, 0), (0, 3), (3, 0), (0, 4), (4, 0),
        (6, 7), (7, 6), (0, 1), (1, 0), (5, 7), (7, 5), (3, 2), (2, 3),
        (1, 5), (5, 1), (6, 0), (0, 6), (8, 2), (2, 8), (0, 5), (5, 0),
        (1, 3), (3, 1), (8, 7), (7, 8), (8, 4), (4, 8), (5, 3), (3, 5),
        (0, 7), (7, 0)
    ]
    
    # Create arrays for start and end days
    s_arr = [Int(f's_{i}') for i in range(9)]
    e_arr = [Int(f'e_{i}') for i in range(9)]
    
    # Create order array (sequence of city visits)
    Order = [Int(f'Order_{i}') for i in range(9)]
    
    solver = Solver()
    
    # Fixed start and end days for Barcelona, Venice, Nice
    solver.add(s_arr[0] == 5, e_arr[0] == 6)   # Barcelona: days 5-6
    solver.add(s_arr[1] == 6, e_arr[1] == 10)  # Venice: days 6-10
    solver.add(s_arr[2] == 23, e_arr[2] == 24) # Nice: days 23-24
    
    # Set required stay duration for all cities
    for i in range(9):
        solver.add(e_arr[i] - s_arr[i] + 1 == required_days_list[i])
        solver.add(s_arr[i] >= 1, s_arr[i] <= 24)
        solver.add(e_arr[i] >= 1, e_arr[i] <= 24)
        solver.add(e_arr[i] >= s_arr[i])
    
    # Order constraints: each Order[i] is a city ID (0-8), all distinct, last city is Nice (id=2)
    for i in range(9):
        solver.add(Order[i] >= 0, Order[i] <= 8)
    solver.add(Distinct(Order))
    solver.add(Order[8] == 2)  # Last city is Nice
    
    # First city starts at day 1
    solver.add(s_arr[Order[0]] == 1)
    
    # Sequence constraint: end day of current city = start day of next city
    for i in range(8):
        solver.add(e_arr[Order[i]] == s_arr[Order[i+1]])
    
    # Flight constraints: consecutive cities must have a direct flight
    for i in range(8):
        constraints = []
        for a, b in allowed_pairs:
            constraints.append(And(Order[i] == a, Order[i+1] == b))
        solver.add(Or(constraints))
    
    # Naples must be visited between days 18-20 (at least one day in this range)
    solver.add(s_arr[3] <= 20)
    solver.add(e_arr[3] >= 18)
    
    # Check for a solution
    if solver.check() == sat:
        m = solver.model()
        order_vals = [m.eval(Order[i]).as_long() for i in range(9)]
        s_vals = [m.eval(s_arr[i]).as_long() for i in range(9)]
        e_vals = [m.eval(e_arr[i]).as_long() for i in range(9)]
        
        itinerary = []
        for i in range(9):
            city_id = order_vals[i]
            s = s_vals[city_id]
            e = e_vals[city_id]
            name = id_to_name[city_id]
            
            # Add entire stay for the city
            if s == e:
                itinerary.append({"day_range": f"Day {s}", "place": name})
            else:
                itinerary.append({"day_range": f"Day {s}-{e}", "place": name})
            
            # Add flight day entries if not the last city
            if i < 8:
                next_city_id = order_vals[i+1]
                next_name = id_to_name[next_city_id]
                itinerary.append({"day_range": f"Day {e}", "place": name})  # Departure
                itinerary.append({"day_range": f"Day {e}", "place": next_name})  # Arrival
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()