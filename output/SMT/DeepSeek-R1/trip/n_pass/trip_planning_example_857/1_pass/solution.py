from z3 import *
import json

def main():
    # Define the cities and their durations
    cities = ['Porto', 'Geneva', 'Mykonos', 'Manchester', 'Hamburg', 'Naples', 'Frankfurt']
    durs_list = [2, 3, 3, 4, 5, 5, 2]  # durations by city index

    # Create solver
    s = Solver()

    # Order variables: 7 integers representing the sequence of cities
    order = [Int('order_%i' % i) for i in range(7)]
    
    # Constraints: each order[i] is between 0 and 6, and all are distinct
    s.add([And(order[i] >= 0, order[i] < 7) for i in range(7)])
    s.add(Distinct(order))

    # Start day variables for each city in the sequence
    start = [Int('start_%i' % i) for i in range(7)]
    
    # Define a function to get duration by city index
    def dur(city_idx):
        return If(city_idx == 0, durs_list[0],
                If(city_idx == 1, durs_list[1],
                If(city_idx == 2, durs_list[2],
                If(city_idx == 3, durs_list[3],
                If(city_idx == 4, durs_list[4],
                If(city_idx == 5, durs_list[5], durs_list[6]))))
    
    # Start day constraints
    s.add(start[0] == 1)
    for i in range(1, 7):
        s.add(start[i] == start[i-1] + dur(order[i-1]) - 1)
    
    # Total trip must end on day 18
    s.add(start[6] + dur(order[6]) - 1 == 18)

    # Flight connections: list of allowed edges (bidirectional)
    edges_by_index = [
        (4, 6), (5, 2), (4, 0), (4, 1), (2, 1), (6, 1), (6, 0), 
        (1, 0), (1, 3), (5, 3), (6, 5), (6, 3), (5, 1), (0, 3), (4, 3)
    ]
    allowed_set = set()
    for a, b in edges_by_index:
        allowed_set.add((a, b))
        allowed_set.add((b, a))
    
    # Constraints for consecutive cities: must have a direct flight
    for i in range(6):
        s.add(Or([And(order[i] == a, order[i+1] == b) for (a, b) in allowed_set]))
    
    # Event constraints
    for j in range(7):
        # Mykonos (index 2) must have start day between 8 and 12
        s.add(If(order[j] == 2, And(start[j] >= 8, start[j] <= 12), True))
        # Manchester (index 3) must start on or after day 12
        s.add(If(order[j] == 3, start[j] >= 12, True))
        # Frankfurt (index 6) must start on day 5
        s.add(If(order[j] == 6, start[j] == 5, True))
    
    # Solve the constraints
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(7)]
        start_vals = [m.evaluate(start[i]).as_long() for i in range(7)]
        
        # Build itinerary
        itinerary = []
        # First city
        idx0 = order_vals[0]
        s0 = start_vals[0]
        e0 = s0 + durs_list[idx0] - 1
        itinerary.append({'day_range': f'Day {s0}-{e0}', 'place': cities[idx0]})
        
        # Subsequent cities
        for i in range(6):
            flight_day = start_vals[i+1]  # same as end day of current city
            # Departure from current city
            itinerary.append({'day_range': f'Day {flight_day}', 'place': cities[order_vals[i]]})
            # Arrival to next city
            itinerary.append({'day_range': f'Day {flight_day}', 'place': cities[order_vals[i+1]]})
            # Entire stay for next city
            s_next = start_vals[i+1]
            idx_next = order_vals[i+1]
            e_next = s_next + durs_list[idx_next] - 1
            itinerary.append({'day_range': f'Day {s_next}-{e_next}', 'place': cities[idx_next]})
        
        # Output as JSON
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()