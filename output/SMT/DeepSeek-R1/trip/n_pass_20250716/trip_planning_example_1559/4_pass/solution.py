from z3 import *

def format_day(day):
    return f"Day {day}"

def format_day_range(start, end):
    if start == end:
        return f"Day {start}"
    else:
        return f"Day {start}-{end}"

def main():
    city_index = {
        'Valencia': 0,
        'Oslo': 1,
        'Lyon': 2,
        'Prague': 3,
        'Paris': 4,
        'Nice': 5,
        'Seville': 6,
        'Tallinn': 7,
        'Mykonos': 8,
        'Lisbon': 9
    }
    index_to_city = {v: k for k, v in city_index.items()}
    
    durations = [
        2,  # Valencia
        3,  # Oslo
        4,  # Lyon
        3,  # Prague
        4,  # Paris
        4,  # Nice
        5,  # Seville
        2,  # Tallinn
        5,  # Mykonos
        2   # Lisbon
    ]
    
    flight_strings = [
        "Lisbon and Paris",
        "Lyon and Nice",
        "Tallinn and Oslo",
        "Prague and Lyon",
        "Paris and Oslo",
        "Lisbon and Seville",
        "Prague and Lisbon",
        "Oslo and Nice",
        "Valencia and Paris",
        "Valencia and Lisbon",
        "Paris and Nice",
        "Nice and Mykonos",
        "Paris and Lyon",
        "Valencia and Lyon",
        "Prague and Oslo",
        "Prague and Paris",
        "Seville and Paris",
        "Oslo and Lyon",
        "Prague and Valencia",
        "Lisbon and Nice",
        "Lisbon and Oslo",
        "Valencia and Seville",
        "Lisbon and Lyon",
        "Paris and Tallinn",
        "Prague and Tallinn"
    ]
    
    neighbors = [[] for _ in range(10)]
    for flight in flight_strings:
        parts = flight.split(' and ')
        c1 = parts[0].strip()
        c2 = parts[1].strip()
        idx1 = city_index[c1]
        idx2 = city_index[c2]
        neighbors[idx1].append(idx2)
        neighbors[idx2].append(idx1)
    
    adj_matrix = [[0]*10 for _ in range(10)]
    for i in range(10):
        for j in neighbors[i]:
            adj_matrix[i][j] = 1

    solver = Solver()
    
    order = [Int('order_%d' % i) for i in range(10)]
    start_at_position = [Int('sp_%d' % i) for i in range(10)]
    
    for i in range(10):
        solver.add(order[i] >= 0, order[i] < 10)
    solver.add(Distinct(order))
    
    dur_array = Array('dur', IntSort(), IntSort())
    for c in range(10):
        solver.add(dur_array[c] == durations[c])
    
    solver.add(start_at_position[0] == 1)
    for i in range(1, 10):
        prev_city = order[i-1]
        d = dur_array[prev_city]
        solver.add(start_at_position[i] == start_at_position[i-1] + d - 1)
    
    start_arr = Array('start_arr', IntSort(), IntSort())
    for i in range(10):
        solver.add(start_arr[order[i]] == start_at_position[i])
    
    seville_idx = city_index['Seville']
    mykonos_idx = city_index['Mykonos']
    valencia_idx = city_index['Valencia']
    oslo_idx = city_index['Oslo']
    
    solver.add(start_arr[seville_idx] == 5)
    solver.add(start_arr[mykonos_idx] == 21)
    solver.add(start_arr[valencia_idx] == 3)
    solver.add(start_arr[oslo_idx] == 13)
    
    solver.add(order[9] == mykonos_idx)
    
    last_city = order[9]
    last_duration = dur_array[last_city]
    solver.add(start_at_position[9] + last_duration - 1 == 25)
    
    for i in range(9):
        city1 = order[i]
        city2 = order[i+1]
        conds = []
        for a in range(10):
            for b in range(10):
                if adj_matrix[a][b] == 1:
                    conds.append(And(city1 == a, city2 == b))
        solver.add(Or(conds))
    
    if solver.check() == sat:
        model = solver.model()
        order_val = [model.evaluate(order[i]).as_long() for i in range(10)]
        start_at_position_val = [model.evaluate(start_at_position[i]).as_long() for i in range(10)]
        
        itinerary = []
        for i in range(10):
            city_idx = order_val[i]
            city_name = index_to_city[city_idx]
            start = start_at_position_val[i]
            end = start + durations[city_idx] - 1
            
            itinerary.append({
                "day_range": format_day_range(start, end),
                "place": city_name
            })
            
            if i < 9:
                itinerary.append({
                    "day_range": format_day(end),
                    "place": city_name
                })
                next_city_idx = order_val[i+1]
                next_city_name = index_to_city[next_city_idx]
                itinerary.append({
                    "day_range": format_day(end),
                    "place": next_city_name
                })
        
        output = {"itinerary": itinerary}
        print(output)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()